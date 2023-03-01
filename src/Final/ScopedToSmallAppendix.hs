{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module Final.ScopedToSmallAppendix where

import Final.DTC
import GHC.Base (ap)
import Data.Functor.Compose (Compose (..))

data EPure a
data SPure a

data Prog sig gam a where
  Pure' :: a -> Prog sig gam a
  Call' :: sig (Prog sig gam a) -> Prog sig gam a
  Enter' :: gam (Prog sig gam (Prog sig gam a)) -> Prog sig gam a

instance (Functor sig, Functor gam) => Functor (Prog sig gam) where
  fmap f (Pure' a) = Pure' (f a)
  fmap f (Call' op) = Call' (fmap (fmap f) op)
  fmap f (Enter' scp) = Enter' (fmap (fmap (fmap f)) scp)

instance (Functor sig, Functor gam) => Applicative (Prog sig gam) where
  pure = Pure'
  (<*>) = ap

instance (Functor sig, Functor gam) => Monad (Prog sig gam) where
  return = pure
  Pure' a >>= f = f a
  Call' op >>= f = Call' (fmap (>>= f) op)
  Enter' scp >>= f = Enter' (fmap (fmap (>>= f)) scp)

data Freer sig gam a where
  Pure :: a -> Freer sig gam a
  Call :: sig x -> (x -> Freer sig gam a) -> Freer sig gam a
  Enter :: gam x -> (x -> Freer sig gam y) -> (y -> Freer sig gam a) -> Freer sig gam a

data Yo f a = Yo { unYo :: forall r. (a -> r) -> f r }
data CoYo f r = forall a. CoYo { unCoYo :: (f a, (a -> r)) }

instance Functor (CoYo f) where
  fmap f (CoYo (y, r)) = CoYo (y, f . r)

freerToProg' :: Freer sig gam a -> Prog (CoYo sig) (CoYo gam) a
freerToProg' (Pure a) = Pure' a
freerToProg' (Call op k) = Call' (fmap (freerToProg' . k) (CoYo (op, id)))
freerToProg' (Enter scp rec k) = Enter' (fmap (fmap (freerToProg' . k) . freerToProg' . rec) (CoYo (scp, id)))

freerToProg :: Freer (Yo sig) (Yo gam) a -> Prog sig gam a
freerToProg (Pure a) = Pure' a
freerToProg (Call (Yo opF) k) = Call' (opF (freerToProg . k))
freerToProg (Enter (Yo scpF) rec k) = Enter' (scpF (freerToProg . fmap (freerToProg . k) . rec))

progToFreer :: (Functor sig, Functor gam) => Prog sig gam a -> Freer (Yo sig) (Yo gam) a
progToFreer (Pure' a) = Pure a
progToFreer (Call' op) = Call (Yo (<$> op)) progToFreer
progToFreer (Enter' scp) = Enter (Yo (<$> scp)) progToFreer progToFreer

progToFreer' :: Prog (CoYo sig) (CoYo gam) a -> Freer sig gam a
progToFreer' (Pure' a) = Pure a
progToFreer' (Call' (CoYo (op, k))) = Call op (progToFreer' . k)
progToFreer' (Enter' (CoYo (scp, k))) = Enter scp (progToFreer' . k) progToFreer'

instance Functor (Freer sig gam) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Call op k) = Call op (fmap f <$> k)
  fmap f (Enter scp k k') = Enter scp k (fmap f <$> k')

instance Applicative (Freer sig gam) where
  pure = Pure
  f <*> a = f >>= (<$> a)

instance Monad (Freer sig gam) where
  return = pure
  Pure a >>= f = f a
  Call op k >>= f = Call op ((>>= f) <$> k)
  Enter scp k k' >>= f = Enter scp k ((>>= f) <$> k')

data ESt a where
  EPut :: Int -> a -> ESt a
  EGet :: (Int -> a) -> ESt a

get :: ESt :<<: sig => Freer sig gam Int
get = Call (inj $ EGet id) return

put :: ESt :<<: sig => Int -> Freer sig gam ()
put n = Call (inj $ EPut n ()) return

safeDiv :: (EThrow :<<: sig, ESt :<<: sig) => Int -> Freer sig gam Int
safeDiv n = do
  s <- get
  if s == 0
    then Call (inj EThrow) return
    else do
      put (n `div` s)
      return (n `div` s)

data EThrow a where
  EThrow :: EThrow a

data SCatch a where
  SCatch :: a -> a -> SCatch a

throw :: EThrow :<<: sig => Freer sig gam a
throw = Call (inj EThrow) return

catch :: SCatch :<<: gam => Freer sig gam a -> Freer sig gam a -> Freer sig gam a
catch h r = Enter (inj $ SCatch h r) id return

data CatchArgs = CatchH | CatchR

catch' :: SCatch :<<: gam => Freer sig gam a -> Freer sig gam a -> Freer sig gam a
catch' h r = Enter (inj $ SCatch CatchH CatchR) (\case
  CatchH -> h
  CatchR -> r) return

prog4 :: (EThrow :<<: sig, ESt :<<: sig, SCatch :<<: gam) => Freer sig gam ()
prog4 = do
  x <- catch (safeDiv 5) (return 42)
  put (x + 1)

data EChoice a where
  EFail :: EChoice a
  EOr :: a -> a -> EChoice a

data EndoAlg eff scp f where
  EndoAlg ::
    { hReturn :: forall x. x -> f x,
      hOps :: forall x w. eff x -> (x -> f w) -> f w,
      hScps :: forall x y w. scp x -> (x -> f y) -> (y -> f w) -> f w
    } ->
    EndoAlg eff scp f

data BaseAlg eff scp f a where
  BaseAlg ::
    { mCall :: forall x. eff x -> (x -> a) -> a
    , mEnter :: forall x y. scp x -> (x -> f y) -> (y -> a) -> a
    } ->
    BaseAlg eff scp f a

hcata :: EndoAlg eff scp f -> Freer eff scp a -> f a
hcata (EndoAlg ret _ _) (Pure x) = ret x
hcata hlr@(EndoAlg{..}) (Call op k) = hOps op (hcata hlr . k)
hcata hlr@(EndoAlg{..}) (Enter scp rec k) = hScps scp (hcata hlr . rec) (hcata hlr . k)

handle :: EndoAlg eff scp f -> BaseAlg eff scp f b -> (a -> b) -> Freer eff scp a -> b
handle hlr mdr gen (Pure x) = gen x
handle hlr mdr@(BaseAlg{..}) gen (Call op k) = mCall op (handle hlr mdr gen . k)
handle hlr mdr@(BaseAlg{..}) gen (Enter scp rec k) = mEnter scp (hcata hlr . rec) (handle hlr mdr gen . k)

handleE :: EndoAlg eff scp f -> Freer eff scp a -> f a
handleE hlr@(EndoAlg{..}) = handle hlr (BaseAlg hOps hScps) hReturn

--handleE' :: EndoAlg eff scp f -> Freer eff scp a -> Freer EPure SPure (f a)
--handleE' hlr e = return (handleE hlr e)

-- Extend basic handling with a function to go back to a program with one less effect
handleE'  ::  EndoAlg sig gam (Compose (Freer sig' gam') f)
          ->  Freer sig gam a
          ->  (Compose (Freer sig' gam') f) a
handleE' = handleE

handleE'' :: (forall x. x -> Freer sig' gam' (f x))
          -> (forall x w. sig x
              -> (x -> Freer sig' gam' (f w))
              -> Freer sig' gam' (f w))
          -> (forall x y w. gam x
              -> (x -> Freer sig' gam' (f y))
              -> (y -> Freer sig' gam' (f w))
              -> Freer sig' gam' (f w))
          -> Freer sig gam a
          -> Freer sig' gam' (f a)
handleE'' hReturn hOps hScps (Pure x) = hReturn x
handleE'' hReturn hOps hScps (Call op k) = hOps op (handleE'' hReturn hOps hScps . k)
handleE'' hReturn hOps hScps (Enter scp rec k) =
  hScps scp (handleE'' hReturn hOps hScps . rec) (handleE'' hReturn hOps hScps . k)

mendingHandle ::
     (forall x. x -> Freer sig' gam' (f x))
  -> (forall x w. sig x -> (x -> Freer sig' gam' (f w)) -> Freer sig' gam' (f w))
  -> (forall x w. gam x -> (x -> Freer sig' gam' (f w)) -> Freer sig' gam' (f w))
  -> (forall x w. f x -> (x -> Freer sig' gam' (f w)) -> Freer sig' gam' (f w))
  -> Freer sig gam a
  -> Freer sig' gam' (f a)
mendingHandle hReturn hOps hScps hMend (Pure x) = hReturn x
mendingHandle hReturn hOps hScps hMend (Call op k) = hOps op (mendingHandle hReturn hOps hScps hMend . k)
mendingHandle hReturn hOps hScps hMend (Enter scp rec k) = do
  fw <- hScps scp (mendingHandle hReturn hOps hScps hMend . rec)
  hMend fw (mendingHandle hReturn hOps hScps hMend . k)

--excH :: EndoAlg (EThrow :++: rs) (SCatch :++: rg) (Compose (Freer rs rg) Maybe)
--excH = EndoAlg (\x -> Compose (return (Just x)))
--  (\_ _ -> Compose $ return Nothing)
--  (\sig rec k -> case sig of
--     Inl (SCatch h r) -> Compose $ do
--       hm <- getCompose $ rec h
--       case hm of
--         Nothing -> _
--         Just v -> _
--     Inr scp -> Compose (Enter scp rec (handlE excH . k)))

prog8 :: Freer EThrow SCatch Int
prog8 = do
  x <- catch throw (return 42)
  return (x + 1)
