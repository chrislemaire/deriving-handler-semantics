{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Final.Writing.AlgebraicFreer where

import Final.DTC
import Control.Monad (liftM, ap, (>=>))
import Prelude hiding (flip)
import Control.Applicative (liftA2)

-- Freer Monad for ops (impure) and values (pure)
data Freer sig a where
  Pure :: a -> Freer sig a
  Impure :: sig x -> (x -> Freer sig a) -> Freer sig a

instance Functor (Freer sig) where
  fmap = liftM

instance Applicative (Freer sig) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer sig) where
  return = pure
  Pure a >>= f = f a
  Impure op k >>= f = Impure op (k >=> f)


data ESt st a where
  Get :: ESt st st
  Put :: st -> ESt st ()

get :: ESt st :<<: sig => Freer sig st
get = Impure (inj Get) return

put :: ESt st :<<: sig => st -> Freer sig ()
put s = Impure (inj $ Put s) return

handleSt :: st -> Freer (ESt st :++: r) a -> Freer r (st, a)
handleSt st (Pure a) = return (st, a)
handleSt st (Impure (Inl Get) k) = handleSt st $ k st
handleSt _ (Impure (Inl (Put st)) k) = handleSt st $ k ()
handleSt st (Impure (Inr op) k) = Impure op (\x -> handleSt st $ k x)


incr :: ESt Int :<<: sig => Freer sig ()
incr = do
  a <- get @Int
  put (a + 1)

stProgram :: Freer (ESt Int :++: EAmb) Int
stProgram = do
  incr; incr; incr
  flip
  get


data EEmpty a
--
--run :: Freer EEmpty a -> a
--run (Pure a) = a
--
--
--stProgram' :: Freer (ESt Int :++: EEmpty) Int
--stProgram' = do
--  incr; incr; incr
--  get
--
--runStProgram' :: (Int, Int)
--runStProgram' = run $ handleSt 0 $ stProgram'
--
data EAmb a where
  Flip :: EAmb Bool

flip :: EAmb :<<: sig => Freer sig Bool
flip = Impure (inj Flip) return

--handleAmb :: Freer (EAmb :++: r) a -> Freer r [a]
--handleAmb (Pure a) = return [a]
--handleAmb (Impure (Inl Flip) k) = liftA2 (<>) (handleAmb $ k True) (handleAmb $ k False)
--handleAmb (Impure (Inr op) k) = Impure op (\x -> handleAmb $ k x)
--
--
--stAmbIs1 :: Freer (ESt Int :++: EAmb :++: EEmpty) Bool
--stAmbIs1 = do
--  _ <- flip
--  incr
--  a <- get @Int
--  if a > 1
--    then return True
--    else return False
--
--runStAmbIs1 :: [(Int, Bool)]
--runStAmbIs1 = run $ handleAmb $ handleSt 0 $ stAmbIs1
---- [(1,False),(1,False)]
--
--ambStIs1 :: Freer (EAmb :++: ESt Int :++: EEmpty) Bool
--ambStIs1 = do
--  _ <- flip
--  incr
--  a <- get @Int
--  if a > 1
--    then return True
--    else return False
--
--runAmbStIs1 :: (Int, [Bool])
--runAmbStIs1 = run $ handleSt 0 $ handleAmb $ ambStIs1
---- (2,[False,True])
--
--handle :: st
--       -> (st -> a -> Freer r w)
--       -> (forall x. st -> eff x -> (st -> x -> Freer r w) -> Freer r w)
--       -> Freer (eff :++: r) a -> Freer r w
--handle st ret _ (Pure a) = ret st a
--handle st ret ops (Impure (Inl op) k) = ops st op (\st' -> handle st' ret ops . k)
--handle st ret ops (Impure (Inr op) k) = Impure op (handle st ret ops . k)
--
--
--handleSt' :: st -> Freer (ESt st :++: r) a -> Freer r (st, a)
--handleSt' initSt = handle initSt
--                          (\st a -> return (st, a))
--                          (\st op k -> case op of
--                              Get -> k st st
--                              Put st' -> k st' ())
--
--handleAmb' :: Freer (EAmb :++: r) a -> Freer r [a]
--handleAmb' = handle ()
--                    (\() a -> return [a])
--                    (\() Flip k -> liftA2 (<>) (k () True) (k () False))
--
--
--handleShallow :: st
--              -> (forall x. st -> x -> Freer r (f x))
--              -> (forall x z. st -> eff x -> (forall y. st -> Freer (eff :++: r) y -> Freer r (f y))
--                                 -> (x -> Freer (eff :++: r) z) -> Freer r (f z))
--              -> Freer (eff :++: r) a -> Freer r (f a)
--handleShallow st ret _ (Pure a) = ret st a
--handleShallow st ret ops (Impure (Inl op) k) = ops st op (\st' -> handleShallow st' ret ops) k
--handleShallow st ret ops (Impure (Inr op) k) = Impure op (handleShallow st ret ops . k)
--
--handleStShallow :: st -> Freer (ESt st :++: r) a -> Freer r (st, a)
--handleStShallow initSt = handleShallow initSt
--                                       (\st a -> return (st, a))
--                                       (\st op hdl k -> case op of
--                                           Get -> hdl st $ k st
--                                           Put st' -> hdl st' $ k ())
--
--handleAmbShallow :: Freer (EAmb :++: r) a -> Freer r [a]
--handleAmbShallow = handleShallow ()
--                                 (\() a -> return [a])
--                                 (\() Flip hdl k -> liftA2 (<>) (hdl () $ k True) (hdl () $ k False))
--
--data Handler st eff r a w =
--  Handler (st -> a -> Freer r w)
--          (forall x. st -> eff x -> (st -> x -> Freer r w) -> Freer r w)
--
--handle' :: st
--        -> Handler st eff r a w
--        -> Freer (eff :++: r) a -> Freer r w
--handle' initSt (Handler ret ops) = handle initSt ret ops
--
--
--stHandler :: Handler st (ESt st) r a (st, a)
--stHandler = Handler (\st a -> return (st, a))
--                    (\st op k -> case op of
--                        Get -> k st st
--                        Put st' -> k st' ())
--
--ambHandler :: Handler () EAmb r a [a]
--ambHandler = Handler (\() a -> return [a])
--                     (\() Flip k -> liftA2 (<>) (k () True) (k () False))


--data AST sig a where
--  ASTValue :: a -> AST sig a
--  ASTOp :: sig x -> (x -> AST sig a) -> AST sig a
--  ASTHandle :: st -> Handler st eff r a w -> AST (eff :++: r) a -> (w -> AST r b) -> AST r b
--
--instance Functor (AST sig) where
--  fmap = liftM
--
--instance Applicative (AST sig) where
--  pure = return
--  (<*>) = ap
--
--instance Monad (AST sig) where
--  return = ASTValue
--  ASTValue a >>= f = f a
--  ASTOp op k >>= f = ASTOp op (k >=> f)
--  ASTHandle st h b k >>= f = ASTHandle st h b (k >=> f)
--
--
--data Handler st eff r a w =
--  Handler (st -> a -> AST r w)
--          (forall x. st -> eff x -> (st -> x -> AST r w) -> AST r w)
--
--handle :: st -> Handler st eff r a w -> AST (eff :++: r) a -> AST r w
--handle st h b = ASTHandle st h b return
--
--get :: ESt st :<<: sig => AST sig st
--get = ASTOp (inj Get) return
--
--put :: ESt st :<<: sig => st -> AST sig ()
--put s = ASTOp (inj $ Put s) return
--
--flip :: EAmb :<<: sig => AST sig Bool
--flip = ASTOp (inj Flip) return
--
--
--incr :: ESt Int :<<: sig => AST sig ()
--incr = do
--  a <- get @Int
--  put (a + 1)
--
--stAmbIs1 :: AST (ESt Int :++: EAmb :++: EEmpty) Bool
--stAmbIs1 = do
--  _ <- flip
--  incr
--  a <- get @Int
--  if a > 1
--    then return True
--    else return False
--
--
--data ValueOrOp sig a where
--  Value :: a -> ValueOrOp sig a
--  Op :: sig x -> (x -> AST sig a) -> ValueOrOp sig a
--
--eval :: AST sig a -> ValueOrOp sig a
--eval (ASTValue a) = Value a
--eval (ASTOp op k) = Op op k
--eval (ASTHandle st h@(Handler ret ops) b k) = case eval b of
--  Value a -> cont (eval $ ret st a) k
--  Op (Inl op) ko -> cont (eval $ ops st op (\st' -> handle st' h . ko)) k
--  Op (Inr op) ko -> Op op (\x -> ASTHandle st h (ko x) k)
--  where
--    cont :: ValueOrOp sig x -> (x -> AST sig a) -> ValueOrOp sig a
--    cont (Value v) c = eval (c v)
--    cont (Op op ko) c = Op op (ko >=> c)

--
--data AST sig a where
--  ASTValue :: a -> AST sig a
--  ASTLet :: AST sig x -> (x -> AST sig a) -> AST sig a
--  ASTOp :: sig x -> AST sig a
--  ASTHandle :: st -> Handler st eff r a w -> AST (eff :++: r) a -> AST r w
--
--instance Functor (AST sig) where
--  fmap = liftM
--
--instance Applicative (AST sig) where
--  pure = return
--  (<*>) = ap
--
--instance Monad (AST sig) where
--  return = ASTValue
--  ASTValue a >>= f = f a
--  ASTLet x k >>= f = ASTLet x (k >=> f)
--  ast >>= f = ASTLet ast f
--
--
--data Handler st eff r a w =
--  Handler (st -> a -> AST r w)
--          (forall x. st -> eff x -> (st -> x -> AST r w) -> AST r w)
--
--data ValueOrOp sig a where
--  Value :: a -> ValueOrOp sig a
--  Op :: sig x -> (x -> AST sig a) -> ValueOrOp sig a
--
--handle = ASTHandle
--
--eval :: AST sig a -> ValueOrOp sig a
--eval (ASTValue a) = Value a
--eval (ASTLet x k) = case eval x of
--  Value a -> eval (k a)
--  Op op ko -> Op op (ko >=> k)
--eval (ASTOp op) = Op op return
--eval (ASTHandle st h@(Handler ret ops) b) = case eval b of
--  Value a -> eval $ ret st a
--  Op (Inl op) ko -> eval $ ops st op (\st' -> handle st' h . ko)
--  Op (Inr op) ko -> Op op (handle st h . ko)

--data Free sig a where
--  Pure :: a -> Free sig a
--  Impure :: sig (Free sig a) -> Free sig a
--
--data Cont sig a where
--   Cont :: sig x -> (x -> Free sig a) -> Cont sig a
--
--instance Functor sig => Functor (Free sig) where
--  fmap f (Pure a) = Pure (f a)
--  fmap f (Impure sig) = Impure (fmap f <$> sig)
--
--instance Functor sig => Applicative (Free sig) where
--  pure = return
--  (<*>) = ap
--
--instance Functor sig => Monad (Free sig) where
--  return = Pure
--  Pure a >>= f = f a
--  Impure sig >>= f = Impure (fmap (>>= f) sig)
--
--data Empty a
--  deriving (Functor)
--
--data Val a where
--  Val :: Int -> (Int -> a) -> Val a
--  deriving (Functor)
--
--data Mul a where
--  Mul :: Int -> Int -> (Int -> a) -> Mul a
--  deriving (Functor)
--
--data Add a where
--  Add :: Int -> Int -> (Int -> a) -> Add a
--  deriving (Functor)
--
--data Flip a where
--  Flip :: (a -> a) -> Flip a
--  deriving (Functor)
--
--
--fmap :: (a -> b) -> (b -> a) -> f a -> f b
--
--val :: Int -> AST Int
--val x = Impure (inj $ Val x return)
--
--mul' :: (Mul :<<: e, Functor e) => Int -> Int -> Free e Int
--mul' l r = Impure (inj $ Mul l r return)
--
--mul :: AST Int -> AST Int -> AST Int
--mul ln rn = ln >>= \l -> rn >>= \r -> Impure (inj $ Mul l r return)
--
--add :: AST Int -> AST Int -> AST Int
--add ln rn = ln >>= \l -> rn >>= \r -> Impure (inj $ Add l r return)
--
--type Exprs = Val :++: Mul :++: Add :++: Flip :++: Empty
--
--type AST = Free Exprs
--
--program :: AST Int
----program = add (mul (val 5) (val 2)) (val 1)
----
--hVal :: Functor e => Free (Val :++: e) Int -> Free e Int
--hVal (Pure a) = Pure a
--hVal (Impure (Inl (Val x k))) = Pure x
--hVal (Impure (Inr e)) = Impure (hVal <$> e)
--
--hMul :: Functor e => Free (Mul :++: e) Int -> Free e Int
--hMul (Pure a) = Pure a
--hMul (Impure (Inl (Mul l r k))) = liftA2 (*) (hMul l) (hMul r)
--hMul (Impure (Inr e)) = Impure (hMul <$> e)
--
--hAdd :: Functor e => Free (Add :++: e) Int -> Free e Int
--hAdd (Pure a) = Pure a
--hAdd (Impure (Inl (Add l r k))) = liftA2 (+) (hAdd l) (hAdd r)
--hAdd (Impure (Inr e)) = Impure (hAdd <$> e)
--
--hPure :: Free Empty a -> a
--hPure (Pure a) = a
--hPure _ = undefined
--
----handleExprs :: AST Int -> Int
----handleExprs = hPure . hAdd . hMul . hVal
--
--eval :: AST Int -> Int
--eval (Pure a) = a
--eval (Impure (Inl (Val x k))) = eval $ k x
--eval (Impure (Inr (Inl (Mul l r k)))) = eval $ k $ l * r
--eval (Impure (Inr (Inr (Inl (Add l r k))))) = eval $ k $ l + r
--eval (Impure (Inr (Inr (Inr (Inl (Flip k)))))) = eval (k 0) `mod` eval (k 1)
--eval (Impure (Inr (Inr (Inr (Inr _))))) = undefined




--data Freer sig a where
--  FPure :: a -> Freer sig a
--  FImpure :: sig x -> (x -> Freer sig a) -> Freer sig a
--
--instance Functor (Freer sig) where
--  fmap f (FPure a) = FPure (f a)
--  fmap f (FImpure x sig) = FImpure x (fmap f <$> sig)
--
--instance Applicative (Freer sig) where
--  pure = return
--  (<*>) = ap
--
--instance Monad (Freer sig) where
--  return = FPure
--  FPure a >>= f = f a
--  FImpure x k >>= f = FImpure x (k >=> f)
--
--data FEmpty a
--
--data FVal a where
--  FVal :: Int -> FVal Int
--
--data FMul a where
--  FMul :: Int -> Int -> FMul Int
--
--data FAdd a where
--  FAdd :: Int -> Int -> FAdd Int
--
--data FFlip a where
--  FFlip :: FFlip Int
--
--fval :: (FVal :<<: e) => Int -> Freer e Int
--fval x = FImpure (inj $ FVal $ x) return
--
--fmul' :: (FMul :<<: e) => Int -> Int -> Freer e Int
--fmul' l r = FImpure (inj $ FMul l r) return
--
--fmul :: (FMul :<<: e) => Freer e Int -> Freer e Int -> Freer e Int
--fmul ln rn = ln >>= \l -> rn >>= \r -> FImpure (inj $ FMul l r) return
--
--fadd :: (FAdd :<<: e) => Freer e Int -> Freer e Int -> Freer e Int
--fadd ln rn = ln >>= \l -> rn >>= \r -> FImpure (inj $ FAdd l r) return
--
--fflip :: (FFlip :<<: e) => Freer e Int
--fflip = FImpure (inj FFlip) return
--
--type FExprs = FVal :++: FMul :++: FAdd :++: FFlip :++: FEmpty
--
--type FAST = Freer FExprs
--
--fprogram :: FAST Int
--fprogram = fadd (fmul (fval 5) (fval 2)) (fval 1)
--
--hFFlip :: Freer (FFlip :++: e) a -> Freer e [a]
--hFFlip (FPure a) = FPure [a]
--hFFlip (FImpure (Inl FFlip) k) = liftA2 (<>) (hFFlip $ k 0) (hFFlip $ k 1)
--hFFlip (FImpure (Inr e) k) = FImpure e (hFFlip <$> k)
--
--hFVal :: Freer (FVal :++: e) Int -> Freer e Int
--hFVal (FPure a) = FPure a
--hFVal (FImpure (Inl (FVal x)) k) = hFVal $ k x
--hFVal (FImpure (Inr e) k) = FImpure e (hFVal <$> k)
--
--hFMul :: Freer (FMul :++: e) Int -> Freer e Int
--hFMul (FPure a) = FPure a
--hFMul (FImpure (Inl (FMul l r)) k) = hFMul $ k $ l * r
--hFMul (FImpure (Inr e) k) = FImpure e (hFMul <$> k)
--
--hFAdd :: Freer (FAdd :++: e) Int -> Freer e Int
--hFAdd (FPure a) = FPure a
--hFAdd (FImpure (Inl (FAdd l r)) k) = hFAdd $ k $ l + r
--hFAdd (FImpure (Inr e) k) = FImpure e (hFAdd <$> k)
--
--handle :: (a -> w)
--       -> (forall x. sig x -> (x -> Freer (sig :++: e) a) -> (Freer (sig :++: e) a -> Freer e w) -> Freer e w)
--       -> Freer (sig :++: e) a -> Freer e w
--handle ret ops (FPure a) = FPure (ret a)
--handle ret ops (FImpure (Inl sig) k) = ops sig k (handle ret ops)
--handle ret ops (FImpure (Inr e) k) = FImpure e (handle ret ops . k)
--
--hFFlip' :: Freer (FFlip :++: e) a -> Freer e [a]
--hFFlip' = handle (:[]) (\FFlip k hdl -> liftA2 (<>) (hdl $ k 0) (hdl $ k 1))
--
--hFVal' :: Freer (FVal :++: e) w -> Freer e w
--hFVal' = handle id (\(FVal x) k hdl -> hdl $ k x)
--
--hFMul' :: Freer (FMul :++: e) w -> Freer e w
--hFMul' = handle id (\(FMul l r) k hdl -> hdl $ k $ l * r)
--
--data Handler sig e a w where
--  Handler :: (a -> w)
--          -> (forall x. sig x -> (x -> AST (sig :++: e) a) -> (AST (sig :++: e) a -> AST e w) -> AST e w)
--          -> Handler sig e a w

--handle' :: Handler sig e a w -> Freer (sig :++: e) a -> Freer e w
--handle' (Handler ret ops) = handle ret ops

--data AST sig a where
--  Return :: a -> AST sig a
--  Let :: AST sig x -> (x -> AST sig a) -> AST sig a
--  Op :: sig a -> AST sig a
--  Handle :: Handler sig e a w -> AST (sig :++: e) a -> AST e w
--
--astMul' :: FMul :<<: e => Int -> Int -> AST e Int
--astMul' l r = Op (inj $ FMul l r)
--
--handle'' :: Handler sig e a w -> AST (sig :++: e) a -> AST e w
--handle'' = Handle
--
--data ValueOrOp sig a where
--  Value :: a -> ValueOrOp sig a
--  Oppy :: sig x -> (x -> AST sig a) -> ValueOrOp sig a
--
--run :: AST FEmpty a -> a
--run ast = case eval ast of
--  Value a -> a
--
--eval :: AST e a -> ValueOrOp e a
--eval (Return a) = Value a
--eval (Let x k) = case eval x of
--  Value a -> eval $ k a
--  Oppy op ko -> Oppy op (\x -> Let (ko x) k)
--eval (Op sig) = Oppy sig Return
--eval (Handle h@(Handler ret ops) b) = case eval b of
--  Value a -> eval $ Return (ret a)
--  Oppy (Inl op) ko -> eval $ ops op ko (Handle h)
--  Oppy (Inr op) ko -> Oppy op (Handle h . ko)
--
--hFPure :: Freer FEmpty a -> a
--hFPure (FPure a) = a
--hFPure _ = undefined

