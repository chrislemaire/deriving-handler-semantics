{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Final.ScopedToSmall where

import Control.Monad (ap, liftM, (>=>))
import Data.List (find)
import Data.Maybe (fromJust)
import Final.DTC

---------------------------------------------------------------
---- Utility functions
---------------------------------------------------------------
firstJusts :: [Maybe a] -> Maybe a
firstJusts [] = Nothing
firstJusts (Nothing : xs) = firstJusts xs
firstJusts (j : _) = j

type Identity a = a

---------------------------------------------------------------
---- Freer version of scoped effects
---------------------------------------------------------------

data Freer sig gam a where
  Pure :: a -> Freer sig gam a
  Call :: sig x -> (x -> Freer sig gam a) -> Freer sig gam a
  Enter :: gam x -> (x -> Freer sig gam y) -> (y -> Freer sig gam a) -> Freer sig gam a

instance Functor (Freer sig gam) where
  fmap = liftM

instance Applicative (Freer sig gam) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer sig gam) where
  return = pure
  Pure a >>= f = f a
  Call op k >>= f = Call op ((>>= f) <$> k)
  Enter scp k k' >>= f = Enter scp k ((>>= f) <$> k')

data EPure a

data SPure a

run :: Freer EPure SPure a -> a
run (Pure a) = a

---------------------------------------------------------------
---- 0 - Abstract handlers from usage
---------------------------------------------------------------
data Handler0 eff r scp rg f where
  Handler0 ::
    { hReturn :: forall x. x -> Freer r rg (f x),
      hOps :: forall x a. eff x -> (x -> Freer r rg (f a)) -> Freer r rg (f a),
      hScp :: forall x y a. scp x -> (x -> Freer r rg (f y)) -> (y -> Freer r rg (f a)) -> Freer r rg (f a),
      hMend :: forall x a. f x -> (x -> Freer r rg (f a)) -> Freer r rg (f a)
    } ->
    Handler0 eff r scp rg f

handle0 :: Handler0 eff r scp rg f -> Freer (eff :++: r) (scp :++: rg) x -> Freer r rg (f x)
handle0 (Handler0 ret _ _ _) (Pure a) = ret a
handle0 h@(Handler0 _ ops _ _) (Call (Inl op) k) = ops op (\x -> handle0 h (k x))
handle0 h (Call (Inr op) k) = Call op (handle0 h . k)
handle0 h@(Handler0 _ _ scps _) (Enter (Inl scp) rec k) = scps scp (handle0 h . rec) (handle0 h . k)
handle0 h@(Handler0 _ _ _ mend) (Enter (Inr scp) rec k) = Enter scp (handle0 h . rec) (\fx -> mend fx (handle0 h . k))

opCall0 :: eff :<<: sig => (x -> eff a) -> Freer sig gam x -> Freer sig gam a
opCall0 eff xt = xt >>= \x -> Call (inj $ eff x) return

scopeCall0 :: scp :<<: gam => (x -> scp y) -> Freer sig gam x -> Freer sig gam (y -> Freer sig gam a) -> Freer sig gam a
scopeCall0 scp xt rect = xt >>= \x -> rect >>= \rec -> Enter (inj $ scp x) rec return

data EThrow a where
  EThrow :: x -> EThrow a

data SCatch a where
  SCatch :: (a, a) -> SCatch a

hExc :: Freer (EThrow :++: r) (SCatch :++: rg) a -> Freer r rg (Maybe a)
hExc = handle0 Handler0 {..}
  where
    hReturn x = return (Just x)
    hOps (EThrow _) _ = return Nothing
    hScp (SCatch (h, r)) rec k = do
      mh <- rec h
      case mh of
        Nothing -> do
          mr <- rec r
          hMend mr k
        Just x -> k x
    hMend Nothing _ = return Nothing
    hMend (Just x) k = k x
  
-- Backwards ported operations for testing purposes
data UnOpOperator0 x a where
  Fst0 :: UnOpOperator0 (x, y) x
  Snd0 :: UnOpOperator0 (x, y) y

data BinOpOperator0 x y a where
  Add0 :: BinOpOperator0 Int Int Int
  Mul0 :: BinOpOperator0 Int Int Int
  Concat0 :: BinOpOperator0 [a] [a] [a]

proxy0 :: (a -> f x) -> Freer sig gam a -> Freer sig gam (f x)
proxy0 prox e = e >>= (\v -> return (prox v))

unproxy0 :: (f a -> y) -> Freer sig gam (f a) -> Freer sig gam y
unproxy0 unp e = e >>= (\f -> return (unp f))

let0 :: Freer sig gam x -> (x -> Freer sig gam a) -> Freer sig gam a
let0 = (>>=)

pair0 :: Freer sig gam x -> Freer sig gam y -> Freer sig gam (x, y)
pair0 ex ey = do
  vx <- ex
  vy <- ey
  return (vx, vy)

uop0 :: UnOpOperator0 x a -> Freer sig gam x -> Freer sig gam a
uop0 uop ex = do
  vx <- ex
  return
    ( ( case uop of
          Fst0 -> fst
          Snd0 -> snd
      )
        vx
    )

bop0 :: Freer sig gam x -> BinOpOperator0 x y a -> Freer sig gam y -> Freer sig gam a
bop0 ex bop ey = do
  vx <- ex
  vy <- ey
  return
    ( ( case bop of
          Add0 -> (+)
          Mul0 -> (*)
          Concat0 -> (<>)
      )
        vx
        vy
    )

cons0 :: Freer sig gam x -> Freer sig gam [x] -> Freer sig gam [x]
cons0 ex exs = do
  vx <- ex
  vxs <- exs
  return (vx : vxs)

list0 :: [Freer sig gam a] -> Freer sig gam [a]
list0 [] = return []
list0 (x : xs) = do
  vx <- x
  vxs <- list0 xs
  return (vx : vxs)

app0 :: Freer sig gam (x -> Freer sig gam a) -> Freer sig gam x -> Freer sig gam a
app0 ef ea = do
  vf <- ef
  va <- ea
  vf va

if0 :: Freer sig gam Bool -> Freer sig gam a -> Freer sig gam a -> Freer sig gam a
if0 c t e = do
  vc <- c
  if vc
    then t
    else e

unSum0 :: Freer sig gam (x :+: y) -> (x -> Freer sig gam a) -> (y -> Freer sig gam a) -> Freer sig gam a
unSum0 e fa fb = do
  v <- e
  case v of
    Inl0 a -> fa a
    Inr0 b -> fb b

unList0 :: Freer sig gam [x] -> Freer sig gam a -> (x -> [x] -> Freer sig gam a) -> Freer sig gam a
unList0 e fn fc = do
  v <- e
  case v of
    [] -> fn
    (x : xs) -> fc x xs

---------------------------------------------------------------
---- 1 - Split OpCall/ScopeCall into Let and OpCall
---------------------------------------------------------------
data Expr1 sig gam a where
  Lit1 :: a -> Expr1 sig gam a
  OpCall1 :: sig a -> Expr1 sig gam a
  ScopeCall1 :: gam x -> (x -> Expr1 sig gam a) -> Expr1 sig gam a
  Let1 :: Expr1 sig gam x -> (x -> Expr1 sig gam a) -> Expr1 sig gam a

instance Functor (Expr1 sig gam) where
  fmap = liftM

instance Applicative (Expr1 sig gam) where
  pure = Lit1
  (<*>) = ap

instance Monad (Expr1 sig gam) where
  return = pure
  Lit1 a >>= f = f a
  OpCall1 op >>= f = Let1 (OpCall1 op) f
  ScopeCall1 scp rec >>= f = Let1 (ScopeCall1 scp rec) f
  Let1 x k >>= f = Let1 x (k >=> f)

data Handler1 eff r scp rg f where
  Handler1 ::
    { hReturn1 :: forall x. x -> Expr1 r rg (f x),
      hOps1 :: forall x a. eff x -> (x -> Expr1 r rg (f a)) -> Expr1 r rg (f a),
      hScp1 :: forall x y a. scp x -> (x -> Expr1 r rg (f y)) -> (y -> Expr1 r rg (f a)) -> Expr1 r rg (f a),
      hMend1 :: forall x a. f x -> (x -> Expr1 r rg (f a)) -> Expr1 r rg (f a)
    } ->
    Handler1 eff r scp rg f

handle1 :: Handler1 eff r scp rg f -> Expr1 (eff :++: r) (scp :++: rg) x -> Expr1 r rg (f x)
handle1 (Handler1 ret _ _ _) (Lit1 a) = ret a
handle1 h@(Handler1 _ ops _ _) (Let1 (OpCall1 (Inl op)) k) = ops op (\x -> handle1 h (k x))
handle1 h (Let1 (OpCall1 (Inr op)) k) = Let1 (OpCall1 op) (handle1 h . k)
handle1 h@(Handler1 _ _ scps _) (Let1 (ScopeCall1 (Inl scp) rec) k) = scps scp (handle1 h . rec) (handle1 h . k)
handle1 h@(Handler1 _ _ _ mend) (Let1 (ScopeCall1 (Inr scp) rec) k) = Let1 (ScopeCall1 scp (handle1 h . rec)) (\fx -> mend fx (handle1 h . k))
-- Added cases
handle1 h (Let1 (Lit1 a) k) = handle1 h (k a)
handle1 h (Let1 (Let1 arg k) k') = handle1 h (Let1 arg (k >=> k'))
handle1 h eb = handle1 h (Let1 eb return)

data Result1 sig gam a where
  NoOp1 :: a -> Result1 sig gam a
  Op1 :: sig x -> (x -> Expr1 sig gam a) -> Result1 sig gam a
  Scope1 :: gam x -> (x -> Expr1 sig gam y) -> (y -> Expr1 sig gam a) -> Result1 sig gam a
  
-- Backwards ported operations for testing purposes
data UnOpOperator1 x a where
  Fst1 :: UnOpOperator1 (x, y) x
  Snd1 :: UnOpOperator1 (x, y) y

data BinOpOperator1 x y a where
  Add1 :: BinOpOperator1 Int Int Int
  Mul1 :: BinOpOperator1 Int Int Int
  Concat1 :: BinOpOperator1 [a] [a] [a]

proxy1 :: (a -> f x) -> Expr1 sig gam a -> Expr1 sig gam (f x)
proxy1 prox e = Let1 e (\v -> Lit1 (prox v))

unproxy1 :: (f a -> y) -> Expr1 sig gam (f a) -> Expr1 sig gam y
unproxy1 unp e = Let1 e (\f -> Lit1 (unp f))

pair1 :: Expr1 sig gam x -> Expr1 sig gam y -> Expr1 sig gam (x, y)
pair1 ex ey = do
  vx <- ex
  vy <- ey
  return (vx, vy)

opCall1 :: eff :<<: sig => (x -> eff a) -> Expr1 sig gam x -> Expr1 sig gam a
opCall1 eff xt = xt >>= \x -> OpCall1 (inj $ eff x)

uop1 :: UnOpOperator1 x a -> Expr1 sig gam x -> Expr1 sig gam a
uop1 uop ex = do
  vx <- ex
  return
    ( ( case uop of
          Fst1 -> fst
          Snd1 -> snd
      )
        vx
    )

bop1 :: Expr1 sig gam x -> BinOpOperator1 x y a -> Expr1 sig gam y -> Expr1 sig gam a
bop1 ex bop ey = do
  vx <- ex
  vy <- ey
  return
    ( ( case bop of
          Add1 -> (+)
          Mul1 -> (*)
          Concat1 -> (<>)
      )
        vx
        vy
    )

cons1 :: Expr1 sig gam x -> Expr1 sig gam [x] -> Expr1 sig gam [x]
cons1 ex exs = do
  vx <- ex
  vxs <- exs
  return (vx : vxs)

list1 :: [Expr1 sig gam a] -> Expr1 sig gam [a]
list1 [] = return []
list1 (x : xs) = do
  vx <- x
  vxs <- list1 xs
  return (vx : vxs)

app1 :: Expr1 sig gam (x -> Expr1 sig gam a) -> Expr1 sig gam x -> Expr1 sig gam a
app1 ef ea = do
  vf <- ef
  va <- ea
  vf va

if1 :: Expr1 sig gam Bool -> Expr1 sig gam a -> Expr1 sig gam a -> Expr1 sig gam a
if1 c t e = do
  vc <- c
  if vc
    then t
    else e

unSum1 :: Expr1 sig gam (x :+: y) -> (x -> Expr1 sig gam a) -> (y -> Expr1 sig gam a) -> Expr1 sig gam a
unSum1 e fa fb = do
  v <- e
  case v of
    Inl0 a -> fa a
    Inr0 b -> fb b

unList1 :: Expr1 sig gam [x] -> Expr1 sig gam a -> (x -> [x] -> Expr1 sig gam a) -> Expr1 sig gam a
unList1 e fn fc = do
  v <- e
  case v of
    [] -> fn
    (x : xs) -> fc x xs


-- Evaluation function
eval1 :: Expr1 sig gam a -> Result1 sig gam a
eval1 (Lit1 a) = NoOp1 a
eval1 (OpCall1 op) = Op1 op return
eval1 (ScopeCall1 scp rec) = Scope1 scp rec return
eval1 (Let1 x k) = case eval1 x of
  NoOp1 xv -> eval1 $ k xv
  Op1 op x_op -> Op1 op (x_op >=> k)
  Scope1 scp rec x_op -> Scope1 scp rec (x_op >=> k)

---------------------------------------------------------------
---- 2 - Lift Handle into Expr
---------------------------------------------------------------
data Expr2 sig gam a where
  Lit2 :: a -> Expr2 sig gam a
  OpCall2 :: sig a -> Expr2 sig gam a
  ScopeCall2 :: gam x -> (x -> Expr2 sig gam a) -> Expr2 sig gam a
  Let2 :: Expr2 sig gam x -> (x -> Expr2 sig gam a) -> Expr2 sig gam a
  Handle2 :: Handler2 eff r scp rg f -> Expr2 (eff :++: r) (scp :++: rg) x -> Expr2 r rg (f x)

instance Functor (Expr2 sig gam) where
  fmap = liftM

instance Applicative (Expr2 sig gam) where
  pure = Lit2
  (<*>) = ap

instance Monad (Expr2 sig gam) where
  return = pure
  Lit2 a >>= f = f a
  OpCall2 op >>= f = Let2 (OpCall2 op) f
  ScopeCall2 scp rec >>= f = Let2 (ScopeCall2 scp rec) f
  Handle2 h eb >>= f = Let2 (Handle2 h eb) f
  Let2 x k >>= f = Let2 x (k >=> f)

data Handler2 eff r scp rg f where
  Handler2 ::
    { hReturn2 :: forall x. x -> Expr2 r rg (f x),
      hOps2 :: forall x a. eff x -> (x -> Expr2 r rg (f a)) -> Expr2 r rg (f a),
      hScp2 :: forall x y a. scp x -> (x -> Expr2 r rg (f y)) -> (y -> Expr2 r rg (f a)) -> Expr2 r rg (f a),
      hMend2 :: forall x a. f x -> (x -> Expr2 r rg (f a)) -> Expr2 r rg (f a)
    } ->
    Handler2 eff r scp rg f

data Result2 sig gam a where
  NoOp2 :: a -> Result2 sig gam a
  Op2 :: sig x -> (x -> Expr2 sig gam a) -> Result2 sig gam a
  Scope2 :: gam x -> (x -> Expr2 sig gam y) -> (y -> Expr2 sig gam a) -> Result2 sig gam a

opCall2 :: eff :<<: sig => (x -> eff a) -> Expr2 sig gam x -> Expr2 sig gam a
opCall2 eff xt = xt >>= \x -> OpCall2 (inj $ eff x)

eval2 :: Expr2 sig gam a -> Result2 sig gam a
eval2 (Lit2 a) = NoOp2 a
eval2 (OpCall2 op) = Op2 op return
eval2 (ScopeCall2 scp rec) = Scope2 scp rec return
eval2 (Let2 x k) = case eval2 x of
  NoOp2 xv -> eval2 $ k xv
  Op2 op x_op -> Op2 op (x_op >=> k)
  Scope2 scp rec x_op -> Scope2 scp rec (x_op >=> k)
-- eval2 (Handle2 h@(Handler2 ret ops scps mend) eb) = eval2 $ case eb of
--  (Lit2 a) -> ret a
--  (Let2 (OpCall2 (Inl op)) k) -> ops op (\x -> Handle2 h (k x))
--  (Let2 (OpCall2 (Inr op)) k) -> Let2 (OpCall2 op) (Handle2 h . k)
--  (Let2 (ScopeCall2 (Inl scp) rec) k) -> scps scp (Handle2 h . rec) (Handle2 h . k)
--  (Let2 (ScopeCall2 (Inr scp) rec) k) -> Let2 (ScopeCall2 scp (Handle2 h . rec)) (\fx -> mend fx (Handle2 h . k))
--  (Let2 (Lit2 a) k) -> Handle2 h (k a)
--  (Let2 (Let2 arg k) k') -> Handle2 h (Let2 arg (k >=> k'))
--  _ -> Handle2 h (Let2 e return)
-- Rewrite desugarings to evaluation
eval2 (Handle2 h@(Handler2 ret ops scps mend) eb) = case eval2 eb of
  NoOp2 a -> eval2 $ ret a
  (Op2 (Inl op) k) -> eval2 $ ops op (\x -> Handle2 h (k x))
  (Op2 (Inr op) k) -> Op2 op (Handle2 h . k)
  (Scope2 (Inl scp) rec k) -> eval2 $ scps scp (Handle2 h . rec) (Handle2 h . k)
  (Scope2 (Inr scp) rec k) -> Scope2 scp (Handle2 h . rec) (\fx -> mend fx (Handle2 h . k))

---------------------------------------------------------------
---- 3.1 - Add standard constructions we wish to be expressions in the language later
---------------------------------------------------------------
data UnOpOperator2 x a where
  Fst2 :: UnOpOperator2 (x, y) x
  Snd2 :: UnOpOperator2 (x, y) y

data BinOpOperator2 x y a where
  Add2 :: BinOpOperator2 Int Int Int
  Mul2 :: BinOpOperator2 Int Int Int
  Concat2 :: BinOpOperator2 [a] [a] [a]

proxy2 :: (a -> f x) -> Expr2 sig gam a -> Expr2 sig gam (f x)
proxy2 prox e = Let2 e (\v -> Lit2 (prox v))

unproxy2 :: (f a -> y) -> Expr2 sig gam (f a) -> Expr2 sig gam y
unproxy2 unp e = Let2 e (\f -> Lit2 (unp f))

pair2 :: Expr2 sig gam x -> Expr2 sig gam y -> Expr2 sig gam (x, y)
pair2 ex ey = do
  vx <- ex
  vy <- ey
  return (vx, vy)

pair2_2 :: Expr2 sig gam x -> Expr2 sig gam y -> Expr2 sig gam (x, y)
pair2_2 ex ey =
  ex >>= \vx ->
    ey >>= \vy ->
      return (vx, vy)

pair2_3 :: Expr2 sig gam x -> Expr2 sig gam y -> Expr2 sig gam (x, y)
pair2_3 ex ey =
  Let2
    ex
    ( \vx ->
        Let2
          ey
          ( \vy ->
              Lit2 (vx, vy)
          )
    )

uop2 :: UnOpOperator2 x a -> Expr2 sig gam x -> Expr2 sig gam a
uop2 uop ex = do
  vx <- ex
  return
    ( ( case uop of
          Fst2 -> fst
          Snd2 -> snd
      )
        vx
    )

bop2 :: Expr2 sig gam x -> BinOpOperator2 x y a -> Expr2 sig gam y -> Expr2 sig gam a
bop2 ex bop ey = do
  vx <- ex
  vy <- ey
  return
    ( ( case bop of
          Add2 -> (+)
          Mul2 -> (*)
          Concat2 -> (<>)
      )
        vx
        vy
    )

cons2 :: Expr2 sig gam x -> Expr2 sig gam [x] -> Expr2 sig gam [x]
cons2 ex exs = do
  vx <- ex
  vxs <- exs
  return (vx : vxs)

list2 :: [Expr2 sig gam a] -> Expr2 sig gam [a]
list2 [] = return []
list2 (x : xs) = do
  vx <- x
  vxs <- list2 xs
  return (vx : vxs)

app2 :: Expr2 sig gam (x -> Expr2 sig gam a) -> Expr2 sig gam x -> Expr2 sig gam a
app2 ef ea = do
  vf <- ef
  va <- ea
  vf va

if2 :: Expr2 sig gam Bool -> Expr2 sig gam a -> Expr2 sig gam a -> Expr2 sig gam a
if2 c t e = do
  vc <- c
  if vc
    then t
    else e

unSum2 :: Expr2 sig gam (x :+: y) -> (x -> Expr2 sig gam a) -> (y -> Expr2 sig gam a) -> Expr2 sig gam a
unSum2 e fa fb = do
  v <- e
  case v of
    Inl0 a -> fa a
    Inr0 b -> fb b

unList2 :: Expr2 sig gam [x] -> Expr2 sig gam a -> (x -> [x] -> Expr2 sig gam a) -> Expr2 sig gam a
unList2 e fn fc = do
  v <- e
  case v of
    [] -> fn
    (x : xs) -> fc x xs

---------------------------------------------------------------
---- 3.2 - Encode those constructions with Values and additional Exprs
---------------------------------------------------------------
data Data a = Data String a

proxy3 :: (Value3 a -> f x) -> Expr3 sig gam a -> Expr3 sig gam (f x)
proxy3 prox e = Let3 e (\v -> Lit3 (ProxyV3 (prox v)))

unproxy3 :: (f a -> Value3 y) -> Expr3 sig gam (f a) -> Expr3 sig gam y
unproxy3 unp e = Let3 e (\(ProxyV3 f) -> Lit3 (unp f))

data Value3 a where
  LambdaV3 :: (Value3 x -> Expr3 sig gam a) -> Value3 (x -> Expr3 sig gam a)
  IntV3 :: Int -> Value3 Int
  BoolV3 :: Bool -> Value3 Bool
  UnitV3 :: Value3 ()
  PairV3 :: Value3 x -> Value3 y -> Value3 (x, y)
  NilV3 :: Value3 [a]
  ConsV3 :: Value3 a -> Value3 [a] -> Value3 [a]
  SumLeftV3 :: Value3 x -> Value3 (x :+: y)
  SumRightV3 :: Value3 y -> Value3 (x :+: y)
  --
  ProxyV3 :: f a -> Value3 (f a)

data UnOpOperator3 x a where
  Fst3 :: UnOpOperator3 (x, y) x
  Snd3 :: UnOpOperator3 (x, y) y

data BinOpOperator3 x y a where
  Concat3 :: BinOpOperator3 [a] [a] [a]
  Add3 :: BinOpOperator3 Int Int Int
  Mul3 :: BinOpOperator3 Int Int Int

data Expr3 sig gam a where
  Lit3 :: Value3 a -> Expr3 sig gam a
  OpCall3 :: sig a -> Expr3 sig gam a
  ScopeCall3 :: gam x -> (Value3 x -> Expr3 sig gam a) -> Expr3 sig gam a
  Let3 :: Expr3 sig gam x -> (Value3 x -> Expr3 sig gam a) -> Expr3 sig gam a
  Handle3 :: Handler3 eff r scp rg f -> Expr3 (eff :++: r) (scp :++: rg) x -> Expr3 r rg (f x)
  --
  App3 :: Expr3 sig gam (x -> Expr3 sig gam a) -> Expr3 sig gam x -> Expr3 sig gam a
  If3 :: Expr3 sig gam Bool -> Expr3 sig gam a -> Expr3 sig gam a -> Expr3 sig gam a
  Pair3 :: Expr3 sig gam x -> Expr3 sig gam y -> Expr3 sig gam (x, y)
  Nil3 :: Expr3 sig gam [a]
  Cons3 :: Expr3 sig gam a -> Expr3 sig gam [a] -> Expr3 sig gam [a]
  UnOp3 :: UnOpOperator3 x a -> Expr3 sig gam x -> Expr3 sig gam a
  BinOp3 :: Expr3 sig gam x -> BinOpOperator3 x y a -> Expr3 sig gam y -> Expr3 sig gam a
  --
  UnSum3 :: Expr3 sig gam (x :+: y) -> (Value3 x -> Expr3 sig gam a) -> (Value3 y -> Expr3 sig gam a) -> Expr3 sig gam a
  UnList3 :: Expr3 sig gam [x] -> Expr3 sig gam a -> (Value3 x -> Value3 [x] -> Expr3 sig gam a) -> Expr3 sig gam a

data Handler3 eff r scp rg f where
  Handler3 ::
    { hReturn3 :: forall x. Value3 x -> Expr3 r rg (f x),
      hOps3 :: forall x a. eff x -> (Value3 x -> Expr3 r rg (f a)) -> Expr3 r rg (f a),
      hScp3 :: forall x y a. scp x -> (Value3 x -> Expr3 r rg (f y)) -> (Value3 y -> Expr3 r rg (f a)) -> Expr3 r rg (f a),
      hMend3 :: forall x a. Value3 (f x) -> (Value3 x -> Expr3 r rg (f a)) -> Expr3 r rg (f a)
    } ->
    Handler3 eff r scp rg f

data Result3 sig gam a where
  NoOp3 :: Value3 a -> Result3 sig gam a
  Op3 :: sig x -> (Value3 x -> Expr3 sig gam a) -> Result3 sig gam a
  Scope3 :: gam x -> (Value3 x -> Expr3 sig gam y) -> (Value3 y -> Expr3 sig gam a) -> Result3 sig gam a

opCall3 :: eff :<<: sig => (Value3 x -> eff a) -> Expr3 sig gam x -> Expr3 sig gam a
opCall3 eff xt = Let3 xt $ \x -> OpCall3 (inj $ eff x)

eval3 :: Expr3 sig gam a -> Result3 sig gam a
eval3 (Lit3 a) = NoOp3 a
eval3 (OpCall3 op) = Op3 op Lit3
eval3 (ScopeCall3 scp rec) = Scope3 scp rec Lit3
eval3 (Let3 x k) = case eval3 x of
  NoOp3 xv -> eval3 $ k xv
  Op3 op x_op -> Op3 op (\t -> Let3 (x_op t) k)
  Scope3 scp rec x_op -> Scope3 scp rec (\t -> Let3 (x_op t) k)
eval3 (Handle3 h@(Handler3 ret ops scps mend) eb) = case eval3 eb of
  NoOp3 a -> eval3 $ ret a
  (Op3 (Inl op) k) -> eval3 $ ops op (\x -> Handle3 h (k x))
  (Op3 (Inr op) k) -> Op3 op (Handle3 h . k)
  (Scope3 (Inl scp) rec k) -> eval3 $ scps scp (Handle3 h . rec) (Handle3 h . k)
  (Scope3 (Inr scp) rec k) -> Scope3 scp (Handle3 h . rec) (\fx -> mend fx (Handle3 h . k))
--
eval3 (If3 ec ei ee) =
  case eval3 ec of
    NoOp3 (BoolV3 c) ->
      if c
        then eval3 ei
        else eval3 ee
    Op3 op x_op -> Op3 op ((\t -> If3 t ei ee) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> If3 t ei ee) . x_op)
eval3 (App3 ef ea) =
  case eval3 ef of
    NoOp3 vf@(LambdaV3 f) ->
      case eval3 ea of
        NoOp3 va -> eval3 (f va)
        Op3 op x_op -> Op3 op ((\t -> App3 (Lit3 vf) t) . x_op)
        Scope3 scp k x_op -> Scope3 scp k ((\t -> App3 (Lit3 vf) t) . x_op)
    Op3 op x_op -> Op3 op ((\t -> App3 t ea) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> App3 t ea) . x_op)
eval3 (Pair3 e1 e2) =
  case eval3 e1 of
    NoOp3 v1 ->
      case eval3 e2 of
        NoOp3 v2 -> NoOp3 (PairV3 v1 v2)
        Op3 op x_op -> Op3 op ((\t -> Pair3 (Lit3 v1) t) . x_op)
        Scope3 scp k x_op -> Scope3 scp k ((\t -> Pair3 (Lit3 v1) t) . x_op)
    Op3 op x_op -> Op3 op ((\t -> Pair3 t e2) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> Pair3 t e2) . x_op)
eval3 Nil3 = NoOp3 NilV3
eval3 (Cons3 e1 e2) =
  case eval3 e1 of
    NoOp3 v1 ->
      case eval3 e2 of
        NoOp3 v2 -> NoOp3 (ConsV3 v1 v2)
        Op3 op x_op -> Op3 op ((\t -> Cons3 (Lit3 v1) t) . x_op)
        Scope3 scp k x_op -> Scope3 scp k ((\t -> Cons3 (Lit3 v1) t) . x_op)
    Op3 op x_op -> Op3 op ((\t -> Cons3 t e2) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> Cons3 t e2) . x_op)
eval3 (UnOp3 uop ex) =
  case eval3 ex of
    NoOp3 vx ->
      NoOp3 $
        ( case uop of
            Fst3 -> \(PairV3 x _) -> x
            Snd3 -> \(PairV3 _ x) -> x
        )
          vx
    Op3 op x_op -> Op3 op ((\t -> UnOp3 uop t) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> UnOp3 uop t) . x_op)
eval3 (BinOp3 ex bop ey) =
  case eval3 ex of
    NoOp3 vx ->
      case eval3 ey of
        NoOp3 vy ->
          NoOp3 $
            ( case bop of
                Add3 -> (\(IntV3 x) (IntV3 y) -> IntV3 (x + y))
                Mul3 -> (\(IntV3 x) (IntV3 y) -> IntV3 (x * y))
                Concat3 -> concatListValues3
            )
              vx
              vy
        Op3 op x_op -> Op3 op ((\t -> BinOp3 (Lit3 vx) bop t) . x_op)
        Scope3 scp k x_op -> Scope3 scp k ((\t -> BinOp3 (Lit3 vx) bop t) . x_op)
    Op3 op x_op -> Op3 op ((\t -> BinOp3 t bop ey) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> BinOp3 t bop ey) . x_op)
--
eval3 (UnSum3 e fl fr) =
  case eval3 e of
    NoOp3 (SumLeftV3 v) -> eval3 (fl v)
    NoOp3 (SumRightV3 v) -> eval3 (fr v)
    Op3 op x_op -> Op3 op ((\t -> UnSum3 t fl fr) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> UnSum3 t fl fr) . x_op)
eval3 (UnList3 e fn fl) =
  case eval3 e of
    NoOp3 NilV3 -> eval3 fn
    NoOp3 (ConsV3 v vs) -> eval3 (fl v vs)
    Op3 op x_op -> Op3 op ((\t -> UnList3 t fn fl) . x_op)
    Scope3 scp k x_op -> Scope3 scp k ((\t -> UnList3 t fn fl) . x_op)

concatListValues3 :: Value3 [a] -> Value3 [a] -> Value3 [a]
concatListValues3 NilV3 NilV3 = NilV3
concatListValues3 NilV3 vs' = vs'
concatListValues3 vs NilV3 = vs
concatListValues3 (ConsV3 v vs) vs' = ConsV3 v (concatListValues3 vs vs')

---------------------------------------------------------------
---- 4 - (Optionally) Remove intrinsic typing
---------------------------------------------------------------
data Value4 where
  LambdaV4 :: (Value4 -> Expr4) -> Value4
  IntV4 :: Int -> Value4
  BoolV4 :: Bool -> Value4
  UnitV4 :: Value4
  PairV4 :: Value4 -> Value4 -> Value4
  NilV4 :: Value4
  ConsV4 :: Value4 -> Value4 -> Value4
  SumLeftV4 :: Value4 -> Value4
  SumRightV4 :: Value4 -> Value4

data UnOpOperator4 = Fst4 | Snd4

data BinOpOperator4 = Concat4 | Add4 | Mul4

data Expr4 where
  Lit4 :: Value4 -> Expr4
  OpCall4 :: String -> String -> Value4 -> Expr4
  ScopeCall4 :: String -> String -> Value4 -> (Value4 -> Expr4) -> Expr4
  Let4 :: Expr4 -> (Value4 -> Expr4) -> Expr4
  Handle4 :: Handler4 -> Expr4 -> Expr4
  --
  App4 :: Expr4 -> Expr4 -> Expr4
  If4 :: Expr4 -> Expr4 -> Expr4 -> Expr4
  Pair4 :: Expr4 -> Expr4 -> Expr4
  Nil4 :: Expr4
  Cons4 :: Expr4 -> Expr4 -> Expr4
  UnOp4 :: UnOpOperator4 -> Expr4 -> Expr4
  BinOp4 :: Expr4 -> BinOpOperator4 -> Expr4 -> Expr4
  --
  UnSum4 :: Expr4 -> (Value4 -> Expr4) -> (Value4 -> Expr4) -> Expr4
  UnList4 :: Expr4 -> Expr4 -> (Value4 -> Value4 -> Expr4) -> Expr4

data Handler4 where
  Handler4 ::
    { hEffName4 :: String,
      hReturn4 :: Value4 -> Expr4,
      hOps4 :: String -> Value4 -> (Value4 -> Expr4) -> Expr4,
      hScp4 :: String -> Value4 -> (Value4 -> Expr4) -> (Value4 -> Expr4) -> Expr4,
      hMend4 :: Value4 -> (Value4 -> Expr4) -> Expr4
    } ->
    Handler4

opCall4 :: String -> String -> Expr4 -> Expr4
opCall4 eff op xt = Let4 xt (\x -> OpCall4 eff op x)

scopeCall4 :: String -> String -> Expr4 -> (Value4 -> Expr4) -> Expr4
scopeCall4 eff op xt rec = Let4 xt (\x -> ScopeCall4 eff op x rec)

data Result4 where
  NoOp4 :: Value4 -> Result4
  Op4 :: String -> String -> Value4 -> (Value4 -> Expr4) -> Result4
  Scope4 :: String -> String -> Value4 -> (Value4 -> Expr4) -> (Value4 -> Expr4) -> Result4

eval4 :: Expr4 -> Result4
eval4 (Lit4 a) = NoOp4 a
eval4 (OpCall4 eff op vo) = Op4 eff op vo Lit4
eval4 (ScopeCall4 eff scp vs rec) = Scope4 eff scp vs rec Lit4
eval4 (Let4 x k) = case eval4 x of
  NoOp4 xv -> eval4 $ k xv
  Op4 eff op vo x_op -> Op4 eff op vo (\t -> Let4 (x_op t) k)
  Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec (\t -> Let4 (x_op t) k)
eval4 (Handle4 h@(Handler4 eff ret ops scps mend) eb) = case eval4 eb of
  NoOp4 a -> eval4 $ ret a
  Op4 eff' op vo k ->
    if eff == eff'
      then eval4 $ ops op vo (\x -> Handle4 h (k x))
      else Op4 eff' op vo (Handle4 h . k)
  Scope4 eff' scp vs rec k ->
    if eff == eff'
      then eval4 $ scps scp vs (Handle4 h . rec) (Handle4 h . k)
      else Scope4 eff' scp vs (Handle4 h . rec) (\fx -> mend fx (Handle4 h . k))
--
eval4 (If4 ec ei ee) =
  case eval4 ec of
    NoOp4 (BoolV4 c) ->
      if c
        then eval4 ei
        else eval4 ee
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> If4 t ei ee) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> If4 t ei ee) . x_op)
eval4 (App4 ef ea) =
  case eval4 ef of
    NoOp4 vf@(LambdaV4 f) ->
      case eval4 ea of
        NoOp4 va -> eval4 (f va)
        Op4 eff op vo x_op -> Op4 eff op vo ((\t -> App4 (Lit4 vf) t) . x_op)
        Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> App4 (Lit4 vf) t) . x_op)
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> App4 t ea) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> App4 t ea) . x_op)
eval4 (Pair4 e1 e2) =
  case eval4 e1 of
    NoOp4 v1 ->
      case eval4 e2 of
        NoOp4 v2 -> NoOp4 (PairV4 v1 v2)
        Op4 eff op vo x_op -> Op4 eff op vo ((\t -> Pair4 (Lit4 v1) t) . x_op)
        Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> Pair4 (Lit4 v1) t) . x_op)
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> Pair4 t e2) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> Pair4 t e2) . x_op)
eval4 Nil4 = NoOp4 NilV4
eval4 (Cons4 e1 e2) =
  case eval4 e1 of
    NoOp4 v1 ->
      case eval4 e2 of
        NoOp4 v2 -> NoOp4 (ConsV4 v1 v2)
        Op4 eff op vo x_op -> Op4 eff op vo ((\t -> Cons4 (Lit4 v1) t) . x_op)
        Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> Cons4 (Lit4 v1) t) . x_op)
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> Cons4 t e2) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> Cons4 t e2) . x_op)
eval4 (UnOp4 uop ex) =
  case eval4 ex of
    NoOp4 vx ->
      NoOp4 $
        ( case uop of
            Fst4 -> \(PairV4 x _) -> x
            Snd4 -> \(PairV4 _ x) -> x
        )
          vx
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> UnOp4 uop t) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> UnOp4 uop t) . x_op)
eval4 (BinOp4 ex bop ey) =
  case eval4 ex of
    NoOp4 vx ->
      case eval4 ey of
        NoOp4 vy ->
          NoOp4 $
            ( case bop of
                Add4 -> (\(IntV4 x) (IntV4 y) -> IntV4 (x + y))
                Mul4 -> (\(IntV4 x) (IntV4 y) -> IntV4 (x * y))
                Concat4 -> concatListValues4
            )
              vx
              vy
        Op4 eff op vo x_op -> Op4 eff op vo ((\t -> BinOp4 (Lit4 vx) bop t) . x_op)
        Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> BinOp4 (Lit4 vx) bop t) . x_op)
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> BinOp4 t bop ey) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> BinOp4 t bop ey) . x_op)
--
eval4 (UnSum4 e fl fr) =
  case eval4 e of
    NoOp4 (SumLeftV4 v) -> eval4 (fl v)
    NoOp4 (SumRightV4 v) -> eval4 (fr v)
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> UnSum4 t fl fr) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> UnSum4 t fl fr) . x_op)
eval4 (UnList4 e fn fl) =
  case eval4 e of
    NoOp4 NilV4 -> eval4 fn
    NoOp4 (ConsV4 v vs) -> eval4 (fl v vs)
    Op4 eff op vo x_op -> Op4 eff op vo ((\t -> UnList4 t fn fl) . x_op)
    Scope4 eff scp vs rec x_op -> Scope4 eff scp vs rec ((\t -> UnList4 t fn fl) . x_op)

concatListValues4 :: Value4 -> Value4 -> Value4
concatListValues4 NilV4 NilV4 = NilV4
concatListValues4 NilV4 vs' = vs'
concatListValues4 vs NilV4 = vs
concatListValues4 (ConsV4 v vs) vs' = ConsV4 v (concatListValues4 vs vs')

---------------------------------------------------------------
---- 5 - Unembed name binding
---------------------------------------------------------------
data Value5
  = LambdaV5 String Expr5
  | IntV5 Int
  | BoolV5 Bool
  | UnitV5
  | PairV5 Value5 Value5
  | NilV5
  | ConsV5 Value5 Value5
  | --
    SumLeftV5 Value5
  | SumRightV5 Value5
  deriving (Eq, Show)

data UnOpOperator5 = Fst5 | Snd5
  deriving (Eq, Show)

data BinOpOperator5 = Concat5 | Add5 | Mul5
  deriving (Eq, Show)

data Expr5
  = Var5 String
  | Closed5 Value5
  | Lit5 Value5
  | OpCall5 String String Expr5
  | ScopeCall5 String String Expr5 String Expr5
  | Let5 Expr5 String Expr5
  | Handle5 Handler5 Expr5
  | --
    App5 Expr5 Expr5
  | If5 Expr5 Expr5 Expr5
  | Pair5 Expr5 Expr5
  | Nil5
  | Cons5 Expr5 Expr5
  | UnOp5 UnOpOperator5 Expr5
  | BinOp5 Expr5 BinOpOperator5 Expr5
  | --
    UnSum5 Expr5 (String, Expr5) (String, Expr5)
  | UnList5 Expr5 Expr5 (String, String, Expr5)
  deriving (Eq, Show)

data Handler5 where
  Handler5 ::
    { hEffName5 :: String,
      hReturn5 :: (String, Expr5),
      hOps5 :: [(String, String, Expr5)],
      hScp5 :: [(String, String, String, Expr5)],
      hMend5 :: (String, Expr5)
    } ->
    Handler5
  deriving (Eq, Show)

data Result5 where
  NoOp5 :: Value5 -> Result5
  Op5 :: String -> String -> Value5 -> (Expr5 -> Expr5) -> Result5
  Scope5 :: String -> String -> Value5 -> String -> Expr5 -> (Expr5 -> Expr5) -> Result5

substValue5 :: String -> Value5 -> Value5 -> Value5
substValue5 x v (LambdaV5 y body)
  | x /= y = LambdaV5 y (subst5 x v body)
  | otherwise = LambdaV5 y body
substValue5 _ _ NilV5 = NilV5
substValue5 _ _ UnitV5 = UnitV5
substValue5 _ _ (BoolV5 b) = BoolV5 b
substValue5 _ _ (IntV5 b) = IntV5 b
substValue5 x v (PairV5 v1 v2) = PairV5 (substValue5 x v v1) (substValue5 x v v2)
substValue5 x v (ConsV5 v1 v2) = ConsV5 (substValue5 x v v1) (substValue5 x v v2)
--
substValue5 x v (SumLeftV5 v') = SumLeftV5 (substValue5 x v v')
substValue5 x v (SumRightV5 v') = SumRightV5 (substValue5 x v v')

subst5 :: String -> Value5 -> Expr5 -> Expr5
subst5 x v (Var5 y)
  | x == y = Closed5 v
  | otherwise = Var5 y
subst5 x v (Lit5 v') = Lit5 (substValue5 x v v')
subst5 _ _ (Closed5 v') = Closed5 v'
subst5 x v (OpCall5 eff op ea) = OpCall5 eff op (subst5 x v ea)
subst5 x v (ScopeCall5 eff scpNm ea recP recB) = ScopeCall5 eff scpNm (subst5 x v ea) recP (if x /= recP then subst5 x v recB else recB)
subst5 x v (Let5 arg y body)
  | x /= y = Let5 (subst5 x v arg) y (subst5 x v body)
  | otherwise = Let5 (subst5 x v arg) y body
subst5 x v (Handle5 (Handler5 eff (retParamNm, retBody) opIs scpIs (mendParamNm, mendBody)) body) =
  Handle5
    ( Handler5
        eff
        ( if x /= retParamNm
            then (retParamNm, subst5 x v retBody)
            else (retParamNm, retBody)
        )
        ( ( \(op, opParamNm, opBody) ->
              if x /= opParamNm && x /= "resume"
                then (op, opParamNm, subst5 x v opBody)
                else (op, opParamNm, opBody)
          )
            <$> opIs
        )
        ( ( \(scpNm, scpParamNm, scpRecNm, recB) ->
              if x /= scpParamNm && x /= "resume"
                then (scpNm, scpParamNm, scpRecNm, subst5 x v recB)
                else (scpNm, scpParamNm, scpRecNm, recB)
          )
            <$> scpIs
        )
        ( if x /= mendParamNm && x /= "resume"
            then (mendParamNm, subst5 x v mendBody)
            else (mendParamNm, mendBody)
        )
    )
    (subst5 x v body)
subst5 x v (If5 ce te ee) = If5 (subst5 x v ce) (subst5 x v te) (subst5 x v ee)
subst5 x v (App5 e1 e2) = App5 (subst5 x v e1) (subst5 x v e2)
subst5 x v (Pair5 e1 e2) = Pair5 (subst5 x v e1) (subst5 x v e2)
subst5 _ _ Nil5 = Nil5
subst5 x v (Cons5 e1 e2) = Cons5 (subst5 x v e1) (subst5 x v e2)
subst5 x v (UnOp5 uop e1) = UnOp5 uop (subst5 x v e1)
subst5 x v (BinOp5 e1 bop e2) = BinOp5 (subst5 x v e1) bop (subst5 x v e2)
--
subst5 x v (UnSum5 e (y, ey) (z, ez)) = UnSum5 (subst5 x v e) (y, if x /= y then subst5 x v ey else ey) (z, if x /= z then subst5 x v ez else ez)
subst5 x v (UnList5 e en (y, z, ec)) = UnList5 (subst5 x v e) (subst5 x v en) (y, z, if x /= y && x /= z then subst5 x v ec else ec)

substAll5 :: [(String, Value5)] -> Expr5 -> Expr5
substAll5 [] = id
substAll5 ((x, v) : repls) = subst5 x v . substAll5 repls

eval5 :: Expr5 -> Result5
eval5 (Closed5 a) = NoOp5 a
eval5 (Lit5 a) = NoOp5 a
eval5 (OpCall5 eff op ea) = case eval5 ea of
  NoOp5 va -> Op5 eff op va id
  Op5 eff' op' vo' x_op -> Op5 eff' op' vo' (\t -> OpCall5 eff op t)
  Scope5 eff' scp' vs' recP' recB' x_op -> Scope5 eff' scp' vs' recP' recB' (\t -> OpCall5 eff op t)
eval5 (ScopeCall5 eff scp ea recP recB) = case eval5 ea of
  NoOp5 va -> Scope5 eff scp va recP recB id
  Op5 eff' op' vo' x_op -> Op5 eff' op' vo' (\t -> ScopeCall5 eff scp t recP recB)
  Scope5 eff' scp' vs' recP' recB' x_op -> Scope5 eff' scp' vs' recP' recB' (\t -> ScopeCall5 eff scp t recP recB)
eval5 (Let5 xA xP xB) = case eval5 xA of
  NoOp5 xv -> eval5 $ subst5 xP xv xB
  Op5 eff op vo x_op -> Op5 eff op vo (\t -> Let5 (x_op t) xP xB)
  Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB (\t -> Let5 (x_op t) xP xB)
eval5 (Handle5 h@(Handler5 eff (retP, retB) ops scps (mendP, mendB)) eb) = case eval5 eb of
  NoOp5 a -> eval5 $ subst5 retP a retB
  Op5 eff' op vo k ->
    if eff == eff'
      then eval5 $ substAll5 [(opParamP, vo), ("resume", LambdaV5 "___x" (Handle5 h (k (Var5 "___x"))))] opBody
      else Op5 eff' op vo (Handle5 h . k)
    where
      (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
  Scope5 eff' scp vs recP recB k ->
    if eff == eff'
      then eval5 $ substAll5 [(scpParamP, vs), (scpRecP, LambdaV5 recP (Handle5 h recB)), ("resume", LambdaV5 "___x" (Handle5 h (k (Var5 "___x"))))] scpB
      else Scope5 eff' scp vs recP (Handle5 h recB) (\fx -> Let5 fx mendP (subst5 "resume" (LambdaV5 "___x" (Handle5 h (k (Var5 "___x")))) mendB))
    where
      (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
--
eval5 (If5 ec ei ee) =
  case eval5 ec of
    NoOp5 (BoolV5 c) ->
      if c
        then eval5 ei
        else eval5 ee
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> If5 t ei ee) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> If5 t ei ee) . x_op)
eval5 (App5 ef ea) =
  case eval5 ef of
    NoOp5 vf@(LambdaV5 param body) ->
      case eval5 ea of
        NoOp5 va -> eval5 (subst5 param va body)
        Op5 eff op vo x_op -> Op5 eff op vo ((\t -> App5 (Lit5 vf) t) . x_op)
        Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> App5 (Lit5 vf) t) . x_op)
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> App5 t ea) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> App5 t ea) . x_op)
eval5 (Pair5 e1 e2) =
  case eval5 e1 of
    NoOp5 v1 ->
      case eval5 e2 of
        NoOp5 v2 -> NoOp5 (PairV5 v1 v2)
        Op5 eff op vo x_op -> Op5 eff op vo ((\t -> Pair5 (Lit5 v1) t) . x_op)
        Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> Pair5 (Lit5 v1) t) . x_op)
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> Pair5 t e2) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> Pair5 t e2) . x_op)
eval5 Nil5 = NoOp5 NilV5
eval5 (Cons5 e1 e2) =
  case eval5 e1 of
    NoOp5 v1 ->
      case eval5 e2 of
        NoOp5 v2 -> NoOp5 (ConsV5 v1 v2)
        Op5 eff op vo x_op -> Op5 eff op vo ((\t -> Cons5 (Lit5 v1) t) . x_op)
        Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> Cons5 (Lit5 v1) t) . x_op)
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> Cons5 t e2) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> Cons5 t e2) . x_op)
eval5 (UnOp5 uop ex) =
  case eval5 ex of
    NoOp5 vx ->
      NoOp5 $
        ( case uop of
            Fst5 -> \(PairV5 x _) -> x
            Snd5 -> \(PairV5 _ x) -> x
        )
          vx
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> UnOp5 uop t) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> UnOp5 uop t) . x_op)
eval5 (BinOp5 ex bop ey) =
  case eval5 ex of
    NoOp5 vx ->
      case eval5 ey of
        NoOp5 vy ->
          NoOp5 $
            ( case bop of
                Add5 -> (\(IntV5 x) (IntV5 y) -> IntV5 (x + y))
                Mul5 -> (\(IntV5 x) (IntV5 y) -> IntV5 (x * y))
                Concat5 -> concatListValues5
            )
              vx
              vy
        Op5 eff op vo x_op -> Op5 eff op vo ((\t -> BinOp5 (Lit5 vx) bop t) . x_op)
        Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> BinOp5 (Lit5 vx) bop t) . x_op)
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> BinOp5 t bop ey) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> BinOp5 t bop ey) . x_op)
--
eval5 (UnSum5 e fl@(x, ex) fr@(y, ey)) =
  case eval5 e of
    NoOp5 (SumLeftV5 v) -> eval5 (subst5 x v ex)
    NoOp5 (SumRightV5 v) -> eval5 (subst5 y v ey)
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> UnSum5 t fl fr) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> UnSum5 t fl fr) . x_op)
eval5 (UnList5 e en fc@(x, y, ec)) =
  case eval5 e of
    NoOp5 NilV5 -> eval5 en
    NoOp5 (ConsV5 v vs) -> eval5 (substAll5 [(x, v), (y, vs)] ec)
    Op5 eff op vo x_op -> Op5 eff op vo ((\t -> UnList5 t en fc) . x_op)
    Scope5 eff scp vs recP recB x_op -> Scope5 eff scp vs recP recB ((\t -> UnList5 t en fc) . x_op)

concatListValues5 :: Value5 -> Value5 -> Value5
concatListValues5 NilV5 NilV5 = NilV5
concatListValues5 NilV5 vs' = vs'
concatListValues5 vs NilV5 = vs
concatListValues5 (ConsV5 v vs) vs' = ConsV5 v (concatListValues5 vs vs')

---------------------------------------------------------------
---- Step 6.1. Turn direct-style into CPS
---------------------------------------------------------------
data Value6
  = LambdaV6 String Expr6
  | IntV6 Int
  | BoolV6 Bool
  | UnitV6
  | PairV6 Value6 Value6
  | NilV6
  | ConsV6 Value6 Value6
  | --
    SumLeftV6 Value6
  | SumRightV6 Value6
  deriving (Eq, Show)

data UnOpOperator6 = Fst6 | Snd6
  deriving (Eq, Show)

data BinOpOperator6 = Concat6 | Add6 | Mul6
  deriving (Eq, Show)

data Case6
  = ConstC6 Value6
  | PairC6 Case6 Case6
  | ConsC6 Case6 Case6
  | NilC6
  | DataC6 String Case6
  | VarC6 String
  deriving (Eq, Show)

data Expr6
  = Var6 String
  | Closed6 Value6
  | Lit6 Value6
  | OpCall6 String String Expr6
  | ScopeCall6 String String Expr6 String Expr6
  | Let6 Expr6 String Expr6
  | Handle6 Handler6 Expr6
  | --
    App6 Expr6 Expr6
  | If6 Expr6 Expr6 Expr6
  | Pair6 Expr6 Expr6
  | Nil6
  | Cons6 Expr6 Expr6
  | UnOp6 UnOpOperator6 Expr6
  | BinOp6 Expr6 BinOpOperator6 Expr6
  | --
    UnSum6 Expr6 (String, Expr6) (String, Expr6)
  | UnList6 Expr6 Expr6 (String, String, Expr6)
  deriving (Eq, Show)

data Handler6 where
  Handler6 ::
    { hEffName6 :: String,
      hReturn6 :: (String, Expr6),
      hOps6 :: [(String, String, Expr6)],
      hScp6 :: [(String, String, String, Expr6)],
      hMend6 :: (String, Expr6)
    } ->
    Handler6
  deriving (Eq, Show)

substValue6 :: String -> Value6 -> Value6 -> Value6
substValue6 x v (LambdaV6 y body)
  | x /= y = LambdaV6 y (subst6 x v body)
  | otherwise = LambdaV6 y body
substValue6 _ _ NilV6 = NilV6
substValue6 _ _ UnitV6 = UnitV6
substValue6 _ _ (BoolV6 b) = BoolV6 b
substValue6 _ _ (IntV6 b) = IntV6 b
substValue6 x v (PairV6 v1 v2) = PairV6 (substValue6 x v v1) (substValue6 x v v2)
substValue6 x v (ConsV6 v1 v2) = ConsV6 (substValue6 x v v1) (substValue6 x v v2)
--
substValue6 x v (SumLeftV6 v') = SumLeftV6 (substValue6 x v v')
substValue6 x v (SumRightV6 v') = SumRightV6 (substValue6 x v v')

subst6 :: String -> Value6 -> Expr6 -> Expr6
subst6 x v (Var6 y)
  | x == y = Closed6 v
  | otherwise = Var6 y
subst6 x v (Lit6 v') = Lit6 (substValue6 x v v')
subst6 _ _ (Closed6 v') = Closed6 v'
subst6 x v (OpCall6 eff op ea) = OpCall6 eff op (subst6 x v ea)
subst6 x v (ScopeCall6 eff scpNm ea recP recB) = ScopeCall6 eff scpNm (subst6 x v ea) recP (if x /= recP then subst6 x v recB else recB)
subst6 x v (Let6 arg y body)
  | x /= y = Let6 (subst6 x v arg) y (subst6 x v body)
  | otherwise = Let6 (subst6 x v arg) y body
subst6 x v (Handle6 (Handler6 eff (retParamNm, retBody) opIs scpIs (mendParamNm, mendBody)) body) =
  Handle6
    ( Handler6
        eff
        ( if x /= retParamNm
            then (retParamNm, (subst6 x v retBody))
            else (retParamNm, retBody)
        )
        ( ( \(op, opParamNm, opBody) ->
              if x /= opParamNm && x /= "resume"
                then (op, opParamNm, (subst6 x v opBody))
                else (op, opParamNm, opBody)
          )
            <$> opIs
        )
        ( ( \(scpNm, scpParamNm, scpRecNm, recB) ->
              if x /= scpParamNm && x /= "resume"
                then (scpNm, scpParamNm, scpRecNm, (subst6 x v recB))
                else (scpNm, scpParamNm, scpRecNm, recB)
          )
            <$> scpIs
        )
        ( if x /= mendParamNm && x /= "resume"
            then (mendParamNm, (subst6 x v mendBody))
            else (mendParamNm, mendBody)
        )
    )
    (subst6 x v body)
subst6 x v (If6 ce te ee) = If6 (subst6 x v ce) (subst6 x v te) (subst6 x v ee)
subst6 x v (App6 e1 e2) = App6 (subst6 x v e1) (subst6 x v e2)
subst6 x v (Pair6 e1 e2) = Pair6 (subst6 x v e1) (subst6 x v e2)
subst6 _ _ Nil6 = Nil6
subst6 x v (Cons6 e1 e2) = Cons6 (subst6 x v e1) (subst6 x v e2)
subst6 x v (UnOp6 uop e1) = UnOp6 uop (subst6 x v e1)
subst6 x v (BinOp6 e1 bop e2) = BinOp6 (subst6 x v e1) bop (subst6 x v e2)
--
subst6 x v (UnSum6 e (y, ey) (z, ez)) = UnSum6 (subst6 x v e) (y, if x /= y then subst6 x v ey else ey) (z, if x /= z then subst6 x v ez else ez)
subst6 x v (UnList6 e en (y, z, ec)) = UnList6 (subst6 x v e) (subst6 x v en) (y, z, if x /= y && x /= z then subst6 x v ec else ec)

substAll6 :: [(String, Value6)] -> Expr6 -> Expr6
substAll6 [] = id
substAll6 ((x, v) : repls) = subst6 x v . substAll6 repls

concatListValues6 :: Value6 -> Value6 -> Value6
concatListValues6 NilV6 NilV6 = NilV6
concatListValues6 NilV6 vs' = vs'
concatListValues6 vs NilV6 = vs
concatListValues6 (ConsV6 v vs) vs' = ConsV6 v (concatListValues6 vs vs')

applyBinOp6 :: Value6 -> BinOpOperator6 -> Value6 -> Value6
applyBinOp6 (IntV6 x) Add6 (IntV6 y) = IntV6 (x + y)
applyBinOp6 (IntV6 x) Mul6 (IntV6 y) = IntV6 (x * y)
applyBinOp6 vx Concat6 vy = concatListValues6 vx vy

applyUnOp6 :: UnOpOperator6 -> Value6 -> Value6
applyUnOp6 Fst6 (PairV6 x _) = x
applyUnOp6 Snd6 (PairV6 _ x) = x

resumption6 :: Handler6 -> (Expr6 -> Expr6) -> Value6
resumption6 h x_op = LambdaV6 "___x" (Handle6 h (x_op (Var6 "___x")))

data Result6 where
  NoOp6 :: Value6 -> Result6
  Op6 :: String -> String -> Value6 -> (Expr6 -> Expr6) -> Result6
  Scope6 :: String -> String -> Value6 -> String -> Expr6 -> (Expr6 -> Expr6) -> Result6

instance Show Result6 where
  show (NoOp6 v) = "NoOp6 " <> show v
  show (Op6 eff op vo _) = "Op6 " <> show eff <> " " <> show op <> " " <> show vo <> " <func>"
  show (Scope6 eff op vo recP recB _) = "Op6 " <> show eff <> " " <> show op <> " " <> show vo <> " " <> show recP <> " " <> show recB <> " <func>"

eval6_1 :: Expr6 -> (Result6 -> a) -> a
eval6_1 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_1 (Closed6 a) k = k $ NoOp6 a
eval6_1 (Lit6 a) k = k $ NoOp6 a
eval6_1 (OpCall6 eff op ea) k =
  let k1 = \case
        NoOp6 va -> k $ Op6 eff op va id
        Op6 eff' op' vo' x_op -> k $ Op6 eff' op' vo' (\t -> OpCall6 eff op t)
        Scope6 eff' scp' vs' recP' recB' x_op -> k $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op t)
  in eval6_1 ea k1
eval6_1 (ScopeCall6 eff scp ea recP recB) k =
  let k1 = \case
        NoOp6 va -> k $ Scope6 eff scp va recP recB id
        Op6 eff' op' vo' x_op -> k $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp t recP recB)
        Scope6 eff' scp' vs' recP' recB' x_op -> k $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp t recP recB)
  in eval6_1 ea k1
eval6_1 (Let6 xA xP xB) k =
  let k1 = \case
        NoOp6 xv -> eval6_1 (subst6 xP xv xB) k
        Op6 eff op vo x_op -> k $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
   in eval6_1 xA k1
eval6_1 (Handle6 h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) k =
  let k1 = \case
        NoOp6 a -> eval6_1 (subst6 retP a retB) k
        Op6 eff' op vo x_op ->
          if eff == eff'
            then eval6_1 (substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
            else k $ Op6 eff' op vo (Handle6 h . x_op)
          where
            (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
        Scope6 eff' scp vs recP recB x_op ->
          if eff == eff'
            then eval6_1 (substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
            else k $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
          where
            (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
   in eval6_1 eb k1
--
eval6_1 (If6 ec ei ee) k =
  let k1 = \case
        NoOp6 (BoolV6 c) ->
          if c
            then eval6_1 ei k
            else eval6_1 ee k
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> If6 t ei ee) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> If6 t ei ee) . x_op)
   in eval6_1 ec k1
eval6_1 (App6 ef ea) k =
  let k1 = \case
        NoOp6 vf@(LambdaV6 param body) ->
          let k2 = \case
                NoOp6 va -> eval6_1 (subst6 param va body) k
                Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> App6 (Lit6 vf) t) . x_op)
                Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> App6 (Lit6 vf) t) . x_op)
           in eval6_1 ea k2
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> App6 t ea) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> App6 t ea) . x_op)
   in eval6_1 ef k1
eval6_1 (Pair6 e1 e2) k =
  let k1 = \case
        NoOp6 v1 ->
          let k2 = \case
                NoOp6 v2 -> k $ NoOp6 (PairV6 v1 v2)
                Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
           in eval6_1 e2 k2
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> Pair6 t e2) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> Pair6 t e2) . x_op)
   in eval6_1 e1 k1
eval6_1 Nil6 k = k $ NoOp6 NilV6
eval6_1 (Cons6 e1 e2) k =
  let k1 = \case
        NoOp6 v1 ->
          let k2 = \case
                NoOp6 v2 -> k $ NoOp6 (ConsV6 v1 v2)
                Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
           in eval6_1 e2 k2
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> Cons6 t e2) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> Cons6 t e2) . x_op)
   in eval6_1 e1 k1
eval6_1 (UnOp6 uop ex) k =
  let k1 = \case
        NoOp6 vx -> k $ NoOp6 $ applyUnOp6 uop vx
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> UnOp6 uop t) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> UnOp6 uop t) . x_op)
   in eval6_1 ex k1
eval6_1 (BinOp6 ex bop ey) k =
  let k1 = \case
        NoOp6 vx ->
          let k2 = \case
                NoOp6 vy -> k $ NoOp6 $ applyBinOp6 vx bop vy
                Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
           in eval6_1 ey k2
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> BinOp6 t bop ey) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> BinOp6 t bop ey) . x_op)
   in eval6_1 ex k1
--
eval6_1 (UnSum6 e fl@(x, ex) fr@(y, ey)) k =
  let k1 = \case
        NoOp6 (SumLeftV6 v) -> eval6_1 (subst6 x v ex) k
        NoOp6 (SumRightV6 v) -> eval6_1 (subst6 y v ey) k
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
   in eval6_1 e k1
eval6_1 (UnList6 e en fc@(x, y, ec)) k =
  let k1 = \case
        NoOp6 NilV6 -> eval6_1 en k
        NoOp6 (ConsV6 v vs) -> eval6_1 (substAll6 [(x, v), (y, vs)] ec) k
        Op6 eff op vo x_op -> k $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
        Scope6 eff scp vs recP recB x_op -> k $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
   in eval6_1 e k1

normalise6_1 :: Expr6 -> Result6
normalise6_1 e = eval6_1 e id

---------------------------------------------------------------
---- Step 6.2. Adding congruence cases where necessary
---------------------------------------------------------------
type K2 = Result6 :+: Expr6

eval6_2 :: Expr6 -> (K2 -> a) -> a
eval6_2 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_2 (Closed6 a) k = k $ inj0 $ NoOp6 a
eval6_2 (Lit6 a) k = k $ inj0 $ NoOp6 a
eval6_2 (OpCall6 eff op ea) k =
  let k1 = \case
        Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
        Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op t)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op t)
        Inr0 ea' -> eval6_2 ea' k1
  in eval6_2 ea k1
eval6_2 (ScopeCall6 eff scp ea recP recB) k =
  let k1 = \case
        Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
        Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp t recP recB)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp t recP recB)
        Inr0 ea' -> eval6_2 ea' k1
  in eval6_2 ea k1
eval6_2 (Let6 xA xP xB) k =
  let k1 = \case
        Inl0 (NoOp6 xv) -> eval6_2 (subst6 xP xv xB) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
        Inr0 xA' -> eval6_2 xA' k1
   in eval6_2 xA k1
eval6_2 (Handle6 h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) k =
  let k1 = \case
        Inl0 (NoOp6 a) -> eval6_2 (subst6 retP a retB) k
        Inl0 (Op6 eff' op vo x_op) ->
          if eff == eff'
            then eval6_2 (substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
            else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
          where
            (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
        Inl0 (Scope6 eff' scp vs recP recB x_op) ->
          if eff == eff'
            then eval6_2 (substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
            else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
          where
            (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
        Inr0 eb' -> eval6_2 eb' k1
   in eval6_2 eb k1
--
eval6_2 (If6 ec ei ee) k =
  let k1 = \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_2 ei k
            else eval6_2 ee k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> If6 t ei ee) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> If6 t ei ee) . x_op)
        Inr0 ec' -> eval6_2 ec' k1
   in eval6_2 ec k1
eval6_2 (App6 ef ea) k =
  let k1 = \case
        Inl0 (NoOp6 vf@(LambdaV6 param body)) ->
          let k2 = \case
                Inl0 (NoOp6 va) -> eval6_2 (subst6 param va body) k
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> App6 (Lit6 vf) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> App6 (Lit6 vf) t) . x_op)
                Inr0 ea' -> eval6_2 ea' k2
           in eval6_2 ea k2
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> App6 t ea) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> App6 t ea) . x_op)
        Inr0 ef' -> eval6_2 ef' k1
   in eval6_2 ef k1
eval6_2 (Pair6 e1 e2) k =
  let k1 = \case
        Inl0 (NoOp6 v1) ->
          let k2 = \case
                Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Inr0 e2' -> eval6_2 e2' k2
           in eval6_2 e2 k2
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Pair6 t e2) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Pair6 t e2) . x_op)
        Inr0 e1' -> eval6_2 e1' k1
   in eval6_2 e1 k1
eval6_2 Nil6 k = k $ inj0 $ NoOp6 NilV6
eval6_2 (Cons6 e1 e2) k =
  let k1 = \case
        Inl0 (NoOp6 v1) ->
          let k2 = \case
                Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Inr0 e2' -> eval6_2 e2' k2
           in eval6_2 e2 k2
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Cons6 t e2) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Cons6 t e2) . x_op)
        Inr0 e1' -> eval6_2 e1' k1
   in eval6_2 e1 k1
eval6_2 (UnOp6 uop ex) k =
  let k1 = \case
        Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnOp6 uop t) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnOp6 uop t) . x_op)
        Inr0 ex' -> eval6_2 ex' k1
   in eval6_2 ex k1
eval6_2 (BinOp6 ex bop ey) k =
  let k1 = \case
        Inl0 (NoOp6 vx) ->
          let k2 = \case
                Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Inr0 ey' -> eval6_2 ey' k2
           in eval6_2 ey k2
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> BinOp6 t bop ey) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> BinOp6 t bop ey) . x_op)
        Inr0 ex' -> eval6_2 ex' k1
   in eval6_2 ex k1
--
eval6_2 (UnSum6 e fl@(x, ex) fr@(y, ey)) k =
  let k1 = \case
        Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_2 (subst6 x v ex) k
        Inl0 (NoOp6 (SumRightV6 v)) -> eval6_2 (subst6 y v ey) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
        Inr0 e' -> eval6_2 e' k1
   in eval6_2 e k1
eval6_2 (UnList6 e en fc@(x, y, ec)) k =
  let k1 = \case
        Inl0 (NoOp6 NilV6) -> eval6_2 en k
        Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_2 (substAll6 [(x, v), (y, vs)] ec) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
        Inr0 e' -> eval6_2 e' k1
   in eval6_2 e k1

normalise6_2 :: Expr6 -> Result6
normalise6_2 e = eval6_2 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_2 e' k

---------------------------------------------------------------
---- Step 6.2. Argument lifting
---------------------------------------------------------------
eval6_3 :: Expr6 -> (K2 -> a) -> a
eval6_3 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_3 (Closed6 a) k = k $ inj0 $ NoOp6 a
eval6_3 (Lit6 a) k = k $ inj0 $ NoOp6 a
eval6_3 (OpCall6 eff op ea) k =
  let k1 eff op = \case
        Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
        Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op t)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op t)
        Inr0 ea' -> eval6_3 ea' (k1 eff op)
  in eval6_3 ea (k1 eff op)
eval6_3 (ScopeCall6 eff scp ea recP recB) k =
  let k1 eff scp recP recB = \case
        Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
        Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp t recP recB)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp t recP recB)
        Inr0 ea' -> eval6_3 ea' (k1 eff scp recP recB)
  in eval6_3 ea (k1 eff scp recP recB)
eval6_3 (Let6 xA xP xB) k =
  let k1 xP xB = \case
        Inl0 (NoOp6 xv) -> eval6_3 (subst6 xP xv xB) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
        Inr0 xA' -> eval6_3 xA' (k1 xP xB)
   in eval6_3 xA (k1 xP xB)
eval6_3 (Handle6 h eb) k =
  let k1 h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) = \case
        Inl0 (NoOp6 a) -> eval6_3 (subst6 retP a retB) k
        Inl0 (Op6 eff' op vo x_op) ->
          if eff == eff'
            then eval6_3 (substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
            else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
          where
            (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
        Inl0 (Scope6 eff' scp vs recP recB x_op) ->
          if eff == eff'
            then eval6_3 (substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
            else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
          where
            (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
        Inr0 eb' -> eval6_3 eb' (k1 h)
   in eval6_3 eb (k1 h)
--
eval6_3 (If6 ec ei ee) k =
  let k1 ei ee = \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_3 ei k
            else eval6_3 ee k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> If6 t ei ee) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> If6 t ei ee) . x_op)
        Inr0 ec' -> eval6_3 ec' (k1 ei ee)
   in eval6_3 ec (k1 ei ee)
eval6_3 (App6 ef ea) k =
  let k1 ea = \case
        Inl0 (NoOp6 (LambdaV6 param body)) ->
          let k2 param body = \case
                Inl0 (NoOp6 va) -> eval6_3 (subst6 param va body) k
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op)
                Inr0 ea' -> eval6_3 ea' (k2 param body)
           in eval6_3 ea (k2 param body)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> App6 t ea) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> App6 t ea) . x_op)
        Inr0 ef' -> eval6_3 ef' (k1 ea)
   in eval6_3 ef (k1 ea)
eval6_3 (Pair6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Inr0 e2' -> eval6_3 e2' (k2 v1)
           in eval6_3 e2 (k2 v1)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Pair6 t e2) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Pair6 t e2) . x_op)
        Inr0 e1' -> eval6_3 e1' (k1 e2)
   in eval6_3 e1 (k1 e2)
eval6_3 Nil6 k = k $ inj0 $ NoOp6 NilV6
eval6_3 (Cons6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Inr0 e2' -> eval6_3 e2' (k2 v1)
           in eval6_3 e2 (k2 v1)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Cons6 t e2) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Cons6 t e2) . x_op)
        Inr0 e1' -> eval6_3 e1' (k1 e2)
   in eval6_3 e1 (k1 e2)
eval6_3 (UnOp6 uop ex) k =
  let k1 uop = \case
        Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnOp6 uop t) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnOp6 uop t) . x_op)
        Inr0 ex' -> eval6_3 ex' (k1 uop)
   in eval6_3 ex (k1 uop)
eval6_3 (BinOp6 ex bop ey) k =
  let k1 bop ey = \case
        Inl0 (NoOp6 vx) ->
          let k2 vx bop = \case
                Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Inr0 ey' -> eval6_3 ey' (k2 vx bop)
           in eval6_3 ey (k2 vx bop)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> BinOp6 t bop ey) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> BinOp6 t bop ey) . x_op)
        Inr0 ex' -> eval6_3 ex' (k1 bop ey)
   in eval6_3 ex (k1 bop ey)
--
eval6_3 (UnSum6 e fl fr) k =
  let k1 fl@(x, ex) fr@(y, ey) = \case
        Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_3 (subst6 x v ex) k
        Inl0 (NoOp6 (SumRightV6 v)) -> eval6_3 (subst6 y v ey) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
        Inr0 e' -> eval6_3 e' (k1 fl fr)
   in eval6_3 e (k1 fl fr)
eval6_3 (UnList6 e en fc) k =
  let k1 en fc@(x, y, ec) = \case
        Inl0 (NoOp6 NilV6) -> eval6_3 en k
        Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_3 (substAll6 [(x, v), (y, vs)] ec) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
        Inr0 e' -> eval6_3 e' (k1 en fc)
   in eval6_3 e (k1 en fc)

normalise6_3 :: Expr6 -> Result6
normalise6_3 e = eval6_3 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_3 e' k

---------------------------------------------------------------
---- Step 6.4. Continuations switch control
---------------------------------------------------------------
eval6_4 :: Expr6 -> (K2 -> a) -> a
eval6_4 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_4 (Closed6 a) k = k $ inj0 $ NoOp6 a
eval6_4 (Lit6 a) k = k $ inj0 $ NoOp6 a
eval6_4 (OpCall6 eff op ea) k =
  let k1 eff op = \case
        Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
        Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op t)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op t)
        Inr0 ea' -> eval6_4 ea' (k1 eff op)
  in k1 eff op (inj0 ea)
eval6_4 (ScopeCall6 eff scp ea recP recB) k =
  let k1 eff scp recP recB = \case
        Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
        Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp t recP recB)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp t recP recB)
        Inr0 ea' -> eval6_4 ea' (k1 eff scp recP recB)
  in k1 eff scp recP recB (inj0 ea)
eval6_4 (Let6 xA xP xB) k =
  let k1 xP xB = \case
        Inl0 (NoOp6 xv) -> eval6_4 (subst6 xP xv xB) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
        Inr0 xA' -> eval6_4 xA' (k1 xP xB)
   in k1 xP xB (inj0 xA)
eval6_4 (Handle6 h eb) k =
  let k1 h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) = \case
        Inl0 (NoOp6 a) -> eval6_4 (subst6 retP a retB) k
        Inl0 (Op6 eff' op vo x_op) ->
          if eff == eff'
            then eval6_4 (substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
            else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
          where
            (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
        Inl0 (Scope6 eff' scp vs recP recB x_op) ->
          if eff == eff'
            then eval6_4 (substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
            else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
          where
            (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
        Inr0 eb' -> eval6_4 eb' (k1 h)
   in k1 h (inj0 eb)
--
eval6_4 (If6 ec ei ee) k =
  let k1 ei ee = \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_4 ei k
            else eval6_4 ee k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> If6 t ei ee) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> If6 t ei ee) . x_op)
        Inr0 ec' -> eval6_4 ec' (k1 ei ee)
   in k1 ei ee (inj0 ec)
eval6_4 (App6 ef ea) k =
  let k1 ea = \case
        Inl0 (NoOp6 (LambdaV6 param body)) ->
          let k2 param body = \case
                Inl0 (NoOp6 va) -> eval6_4 (subst6 param va body) k
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op)
                Inr0 ea' -> eval6_4 ea' (k2 param body)
           in k2 param body (inj0 ea)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> App6 t ea) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> App6 t ea) . x_op)
        Inr0 ef' -> eval6_4 ef' (k1 ea)
   in k1 ea (inj0 ef)
eval6_4 (Pair6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
                Inr0 e2' -> eval6_4 e2' (k2 v1)
           in k2 v1 (inj0 e2)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Pair6 t e2) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Pair6 t e2) . x_op)
        Inr0 e1' -> eval6_4 e1' (k1 e2)
   in k1 e2 (inj0 e1)
eval6_4 Nil6 k = k $ inj0 $ NoOp6 NilV6
eval6_4 (Cons6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
                Inr0 e2' -> eval6_4 e2' (k2 v1)
           in k2 v1 (inj0 e2)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> Cons6 t e2) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> Cons6 t e2) . x_op)
        Inr0 e1' -> eval6_4 e1' (k1 e2)
   in k1 e2 (inj0 e1)
eval6_4 (UnOp6 uop ex) k =
  let k1 uop = \case
        Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnOp6 uop t) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnOp6 uop t) . x_op)
        Inr0 ex' -> eval6_4 ex' (k1 uop)
   in k1 uop (inj0 ex)
eval6_4 (BinOp6 ex bop ey) k =
  let k1 bop ey = \case
        Inl0 (NoOp6 vx) ->
          let k2 vx bop = \case
                Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
                Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
                Inr0 ey' -> eval6_4 ey' (k2 vx bop)
           in eval6_4 ey (k2 vx bop)
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> BinOp6 t bop ey) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> BinOp6 t bop ey) . x_op)
        Inr0 ex' -> eval6_4 ex' (k1 bop ey)
   in k1 bop ey (inj0 ex)
--
eval6_4 (UnSum6 e fl fr) k =
  let k1 fl@(x, ex) fr@(y, ey) = \case
        Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_4 (subst6 x v ex) k
        Inl0 (NoOp6 (SumRightV6 v)) -> eval6_4 (subst6 y v ey) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
        Inr0 e' -> eval6_4 e' (k1 fl fr)
   in k1 fl fr (inj0 e)
eval6_4 (UnList6 e en fc) k =
  let k1 en fc@(x, y, ec) = \case
        Inl0 (NoOp6 NilV6) -> eval6_4 en k
        Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_4 (substAll6 [(x, v), (y, vs)] ec) k
        Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
        Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
        Inr0 e' -> eval6_4 e' (k1 en fc)
   in k1 en fc (inj0 e)

normalise6_4 :: Expr6 -> Result6
normalise6_4 e = eval6_4 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_4 e' k

---------------------------------------------------------------
---- Step 6.5. Defunctionalisation
---------------------------------------------------------------
data Continuation5
  = Cont5Let String Expr6 K2
  | Cont5OpCall String String K2
  | Cont5ScopeCall String String String Expr6 K2
  | Cont5Handle Handler6 K2
  | Cont5If Expr6 Expr6 K2
  | Cont5App1 Expr6 K2
  | Cont5App2 String Expr6 K2
  | Cont5Pair1 Expr6 K2
  | Cont5Pair2 Value6 K2
  | Cont5Cons1 Expr6 K2
  | Cont5Cons2 Value6 K2
  | Cont5UnOp UnOpOperator6 K2
  | Cont5BinOp1 BinOpOperator6 Expr6 K2
  | Cont5BinOp2 Value6 BinOpOperator6 K2
  | --
    Cont5UnSum (String, Expr6) (String, Expr6) K2
  | Cont5UnList Expr6 (String, String, Expr6) K2

apply6_5 :: Continuation5 -> (K2 -> a) -> a
apply6_5 (Cont5Let xP xB xA) k = case xA of
  Inl0 (NoOp6 xv) -> eval6_5 (subst6 xP xv xB) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
  Inr0 xA' -> eval6_5 xA' (\xA'' -> apply6_5 (Cont5Let xP xB xA'') k)
apply6_5 (Cont5OpCall eff op ea) k = case ea of
  Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
  Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op t)
  Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op t)
  Inr0 ea' -> eval6_5 ea' (\ea'' -> apply6_5 (Cont5OpCall eff op ea'') k)
apply6_5 (Cont5ScopeCall eff scp recP recB ea) k = case ea of
  Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
  Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp t recP recB)
  Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp t recP recB)
  Inr0 ea' -> eval6_5 ea' (\ea'' -> apply6_5 (Cont5ScopeCall eff scp recP recB ea'') k)
apply6_5 (Cont5Handle h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) k = case eb of
  Inl0 (NoOp6 a) -> eval6_5 (subst6 retP a retB) k
  Inl0 (Op6 eff' op vo x_op) ->
    if eff == eff'
      then eval6_5 (substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
      else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
    where
      (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
  Inl0 (Scope6 eff' scp vs recP recB x_op) ->
    if eff == eff'
      then eval6_5 (substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
      else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
    where
      (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
  Inr0 eb' -> eval6_5 eb' (\eb'' -> apply6_5 (Cont5Handle h eb'') k)
--
apply6_5 (Cont5If ei ee ec) k = case ec of
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_5 ei k
      else eval6_5 ee k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> If6 t ei ee) . x_op)
  Inr0 ec' -> eval6_5 ec' (\ec'' -> apply6_5 (Cont5If ei ee ec'') k)
apply6_5 (Cont5App1 ea ef) k = case ef of
  Inl0 (NoOp6 (LambdaV6 param f)) -> apply6_5 (Cont5App2 param f (inj0 ea)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 t ea) . x_op)
  Inr0 e1' -> eval6_5 e1' (\e1'' -> apply6_5 (Cont5App1 ea e1'') k)
apply6_5 (Cont5App2 param f ea) k = case ea of
  Inl0 (NoOp6 va) -> eval6_5 (subst6 param va f) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
  Inr0 e2' -> eval6_5 e2' (\e2'' -> apply6_5 (Cont5App2 param f e2'') k)
apply6_5 (Cont5Pair1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_5 (Cont5Pair2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 t e2) . x_op)
  Inr0 e1' -> eval6_5 e1' (\e1'' -> apply6_5 (Cont5Pair1 e2 e1'') k)
apply6_5 (Cont5Pair2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
  Inr0 e2' -> eval6_5 e2' (\e2'' -> apply6_5 (Cont5Pair2 v1 e2'') k)
apply6_5 (Cont5Cons1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_5 (Cont5Cons2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 t e2) . x_op)
  Inr0 e1' -> eval6_5 e1' (\e1'' -> apply6_5 (Cont5Cons1 e2 e1'') k)
apply6_5 (Cont5Cons2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
  Inr0 e2' -> eval6_5 e2' (\e2'' -> apply6_5 (Cont5Cons2 v1 e2'') k)
apply6_5 (Cont5UnOp uop ex) k = case ex of
  Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> UnOp6 uop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> UnOp6 uop t) . x_op)
  Inr0 ex' -> eval6_5 ex' (\ex'' -> apply6_5 (Cont5UnOp uop ex'') k)
apply6_5 (Cont5BinOp1 bop ey ex) k = case ex of
  Inl0 (NoOp6 vx) -> apply6_5 (Cont5BinOp2 vx bop (inj0 ey)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 t bop ey) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 t bop ey) . x_op)
  Inr0 ex' -> eval6_5 ex' (\ex'' -> apply6_5 (Cont5BinOp1 bop ey ex'') k)
apply6_5 (Cont5BinOp2 vx bop ey) k = case ey of
  Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
  Inr0 ey' -> eval6_5 ey' (\ey'' -> apply6_5 (Cont5BinOp2 vx bop ey'') k)
--
apply6_5 (Cont5UnSum fl@(x, ex) fr@(y, ey) e) k = case e of
  Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_5 (subst6 x v ex) k
  Inl0 (NoOp6 (SumRightV6 v)) -> eval6_5 (subst6 y v ey) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
  Inr0 e' -> eval6_5 e' (\e'' -> apply6_5 (Cont5UnSum fl fr e'') k)
apply6_5 (Cont5UnList en fc@(x, y, ec) e) k = case e of
  Inl0 (NoOp6 NilV6) -> eval6_5 en k
  Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_5 (substAll6 [(x, v), (y, vs)] ec) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
  Inr0 e' -> eval6_5 e' (\e'' -> apply6_5 (Cont5UnList en fc e'') k)

eval6_5 :: Expr6 -> (K2 -> a) -> a
eval6_5 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_5 (Closed6 a) k = k $ inj0 $ NoOp6 a
eval6_5 (Lit6 a) k = k $ inj0 $ NoOp6 a
eval6_5 (OpCall6 eff op ea) k = apply6_5 (Cont5OpCall eff op (inj0 ea)) k
eval6_5 (ScopeCall6 eff scp ea recP recB) k = apply6_5 (Cont5ScopeCall eff scp recP recB (inj0 ea)) k
eval6_5 (Let6 xA xP xB) k = apply6_5 (Cont5Let xP xB (inj0 xA)) k
eval6_5 (Handle6 h eb) k = apply6_5 (Cont5Handle h (inj0 eb)) k
--
eval6_5 (If6 ec ei ee) k = apply6_5 (Cont5If ei ee (inj0 ec)) k
eval6_5 (App6 ef ea) k = apply6_5 (Cont5App1 ea (inj0 ef)) k
eval6_5 (Pair6 e1 e2) k = apply6_5 (Cont5Pair1 e2 (inj0 e1)) k
eval6_5 Nil6 k = k $ inj0 $ NoOp6 NilV6
eval6_5 (Cons6 e1 e2) k = apply6_5 (Cont5Cons1 e2 (inj0 e1)) k
eval6_5 (UnOp6 uop ex) k = apply6_5 (Cont5UnOp uop (inj0 ex)) k
eval6_5 (BinOp6 ex bop ey) k = apply6_5 (Cont5BinOp1 bop ey (inj0 ex)) k
--
eval6_5 (UnSum6 e fl fr) k = apply6_5 (Cont5UnSum fl fr (inj0 e)) k
eval6_5 (UnList6 e en fc) k = apply6_5 (Cont5UnList en fc (inj0 e)) k

normalise6_5 :: Expr6 -> Result6
normalise6_5 e = eval6_5 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_5 e' k

---------------------------------------------------------------
---- Step 6.6. Remove tail-calls
---------------------------------------------------------------
data Continuation6
  = Cont6Let String Expr6 K6
  | Cont6OpCall String String K6
  | Cont6ScopeCall String String String Expr6 K6
  | Cont6Handle Handler6 K6
  | Cont6If Expr6 Expr6 K6
  | Cont6App1 Expr6 K6
  | Cont6App2 String Expr6 K6
  | Cont6Pair1 Expr6 K6
  | Cont6Pair2 Value6 K6
  | Cont6Cons1 Expr6 K6
  | Cont6Cons2 Value6 K6
  | Cont6UnOp UnOpOperator6 K6
  | Cont6BinOp1 BinOpOperator6 Expr6 K6
  | Cont6BinOp2 Value6 BinOpOperator6 K6
  | --
    Cont6UnSum (String, Expr6) (String, Expr6) K6
  | Cont6UnList Expr6 (String, String, Expr6) K6

type K6 = Result6 :+: Expr6 :+: Continuation6

apply6_6 :: Continuation6 -> (K6 -> a) -> a
apply6_6 (Cont6Let xP xB xA) k = case xA of
  Inl0 (NoOp6 xv) -> eval6_6 (inj0 $ subst6 xP xv xB) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
  Inr0 xA' -> eval6_6 xA' (\xA'' -> k (inj0 $ Cont6Let xP xB xA''))
apply6_6 (Cont6OpCall eff op ea) k = case ea of
  Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
  Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op (x_op t))
  Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op (x_op t))
  Inr0 ea' -> eval6_6 ea' (\ea'' -> k (inj0 $ Cont6OpCall eff op ea''))
apply6_6 (Cont6ScopeCall eff scp recP recB ea) k = case ea of
  Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
  Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
  Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
  Inr0 ea' -> eval6_6 ea' (\ea'' -> k (inj0 $ Cont6ScopeCall eff scp recP recB ea''))
apply6_6 (Cont6Handle h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) k = case eb of
  Inl0 (NoOp6 a) -> eval6_6 (inj0 $ subst6 retP a retB) k
  Inl0 (Op6 eff' op vo x_op) ->
    if eff == eff'
      then eval6_6 (inj0 $ substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
      else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
    where
      (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
  Inl0 (Scope6 eff' scp vs recP recB x_op) ->
    if eff == eff'
      then eval6_6 (inj0 $ substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
      else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
    where
      (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
  Inr0 eb' -> eval6_6 eb' (\eb'' -> k (inj0 $ Cont6Handle h eb''))
--
apply6_6 (Cont6If ei ee ec) k = case ec of
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_6 (inj0 ei) k
      else eval6_6 (inj0 ee) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> If6 t ei ee) . x_op)
  Inr0 ec' -> eval6_6 ec' (\ec'' -> k (inj0 $ Cont6If ei ee ec''))
apply6_6 (Cont6App1 ea ef) k = case ef of
  Inl0 (NoOp6 (LambdaV6 param f)) -> apply6_6 (Cont6App2 param f (inj0 ea)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 t ea) . x_op)
  Inr0 e1' -> eval6_6 e1' (\e1'' -> k (inj0 $ Cont6App1 ea e1''))
apply6_6 (Cont6App2 param f ea) k = case ea of
  Inl0 (NoOp6 va) -> eval6_6 (inj0 $ subst6 param va f) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
  Inr0 e2' -> eval6_6 e2' (\e2'' -> k (inj0 $ Cont6App2 param f e2''))
apply6_6 (Cont6Pair1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_6 (Cont6Pair2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 t e2) . x_op)
  Inr0 e1' -> eval6_6 e1' (\e1'' -> k (inj0 $ Cont6Pair1 e2 e1''))
apply6_6 (Cont6Pair2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
  Inr0 e2' -> eval6_6 e2' (\e2'' -> k (inj0 $ Cont6Pair2 v1 e2''))
apply6_6 (Cont6Cons1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_6 (Cont6Cons2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 t e2) . x_op)
  Inr0 e1' -> eval6_6 e1' (\e1'' -> k (inj0 $ Cont6Cons1 e2 e1''))
apply6_6 (Cont6Cons2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
  Inr0 e2' -> eval6_6 e2' (\e2'' -> k (inj0 $ Cont6Cons2 v1 e2''))
apply6_6 (Cont6UnOp uop ex) k = case ex of
  Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> UnOp6 uop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> UnOp6 uop t) . x_op)
  Inr0 ex' -> eval6_6 ex' (\ex'' -> k (inj0 $ Cont6UnOp uop ex''))
apply6_6 (Cont6BinOp1 bop ey ex) k = case ex of
  Inl0 (NoOp6 vx) -> apply6_6 (Cont6BinOp2 vx bop (inj0 ey)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 t bop ey) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 t bop ey) . x_op)
  Inr0 ex' -> eval6_6 ex' (\ex'' -> k (inj0 $ Cont6BinOp1 bop ey ex''))
apply6_6 (Cont6BinOp2 vx bop ey) k = case ey of
  Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
  Inr0 ey' -> eval6_6 ey' (\ey'' -> k (inj0 $ Cont6BinOp2 vx bop ey''))
--
apply6_6 (Cont6UnSum fl@(x, ex) fr@(y, ey) e) k = case e of
  Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_6 (inj0 $ subst6 x v ex) k
  Inl0 (NoOp6 (SumRightV6 v)) -> eval6_6 (inj0 $ subst6 y v ey) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
  Inr0 e' -> eval6_6 e' (\e'' -> k (inj0 $ Cont6UnSum fl fr e''))
apply6_6 (Cont6UnList en fc@(x, y, ec) e) k = case e of
  Inl0 (NoOp6 NilV6) -> eval6_6 (inj0 en) k
  Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_6 (inj0 $ substAll6 [(x, v), (y, vs)] ec) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
  Inr0 e' -> eval6_6 e' (\e'' -> k (inj0 $ Cont6UnList en fc e''))

eval6_6 :: (Expr6 :+: Continuation6) -> (K6 -> a) -> a
eval6_6 (Inr0 c) k = apply6_6 c k
eval6_6 (Inl0 (Var6 nm)) _ = error ("Free variable: " <> nm)
eval6_6 (Inl0 (Closed6 a)) k = k $ inj0 $ NoOp6 a
eval6_6 (Inl0 (Lit6 a)) k = k $ inj0 $ NoOp6 a
eval6_6 (Inl0 (OpCall6 eff op ea)) k = apply6_6 (Cont6OpCall eff op (inj0 ea)) k
eval6_6 (Inl0 (ScopeCall6 eff scp ea recP recB)) k = apply6_6 (Cont6ScopeCall eff scp recP recB (inj0 ea)) k
eval6_6 (Inl0 (Let6 xA xP xB)) k = apply6_6 (Cont6Let xP xB (inj0 xA)) k
eval6_6 (Inl0 (Handle6 h eb)) k = apply6_6 (Cont6Handle h (inj0 eb)) k
--
eval6_6 (Inl0 (If6 ec ei ee)) k = apply6_6 (Cont6If ei ee (inj0 ec)) k
eval6_6 (Inl0 (App6 ef ea)) k = apply6_6 (Cont6App1 ea (inj0 ef)) k
eval6_6 (Inl0 (Pair6 e1 e2)) k = apply6_6 (Cont6Pair1 e2 (inj0 e1)) k
eval6_6 (Inl0 Nil6) k = k $ inj0 $ NoOp6 NilV6
eval6_6 (Inl0 (Cons6 e1 e2)) k = apply6_6 (Cont6Cons1 e2 (inj0 e1)) k
eval6_6 (Inl0 (UnOp6 uop ex)) k = apply6_6 (Cont6UnOp uop (inj0 ex)) k
eval6_6 (Inl0 (BinOp6 ex bop ey)) k = apply6_6 (Cont6BinOp1 bop ey (inj0 ex)) k
--
eval6_6 (Inl0 (UnSum6 e fl fr)) k = apply6_6 (Cont6UnSum fl fr (inj0 e)) k
eval6_6 (Inl0 (UnList6 e en fc)) k = apply6_6 (Cont6UnList en fc (inj0 e)) k

normalise6_6 :: Expr6 -> Result6
normalise6_6 e = eval6_6 (inj0 e) k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_6 e' k

---------------------------------------------------------------
---- Step 6.7. Turn continuations into terms
---------------------------------------------------------------
data Continuation7
  = Cont7Let String Expr6 K7
  | Cont7OpCall String String K7
  | Cont7ScopeCall String String String Expr6 K7
  | Cont7Handle Handler6 K7
  | Cont7If Expr6 Expr6 K7
  | Cont7App1 Expr6 K7
  | Cont7App2 String Expr6 K7
  | Cont7Pair1 Expr6 K7
  | Cont7Pair2 Value6 K7
  | Cont7Cons1 Expr6 K7
  | Cont7Cons2 Value6 K7
  | Cont7UnOp UnOpOperator6 K7
  | Cont7BinOp1 BinOpOperator6 Expr6 K7
  | Cont7BinOp2 Value6 BinOpOperator6 K7
  | --
    Cont7UnSum (String, Expr6) (String, Expr6) K7
  | Cont7UnList Expr6 (String, String, Expr6) K7

type K7 = Result6 :+: Expr6

apply6_7 :: Continuation7 -> (K7 -> a) -> a
apply6_7 (Cont7Let xP xB xA) k = case xA of
  Inl0 (NoOp6 xv) -> eval6_7 (inj0 $ subst6 xP xv xB) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
  Inr0 xA' -> eval6_7 xA' $ \case
    Inl0 (NoOp6 xv) -> eval6_7 (inj0 $ subst6 xP xv xB) k
    Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
    Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
    Inr0 xA'' -> k (inj0 $ Let6 xA'' xP xB)
apply6_7 (Cont7OpCall eff op ea) k = case ea of
  Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
  Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op (x_op t))
  Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op (x_op t))
  Inr0 ea' -> eval6_7 ea' $ \case
    Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
    Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op (x_op t))
    Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op (x_op t))
    Inr0 ea'' -> k (inj0 $ OpCall6 eff op ea'')
apply6_7 (Cont7ScopeCall eff scp recP recB ea) k = case ea of
  Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
  Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
  Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
  Inr0 ea' -> eval6_7 ea' $ \case
    Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
    Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
    Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
    Inr0 ea'' -> k (inj0 $ ScopeCall6 eff scp ea'' recP recB)
apply6_7 (Cont7Handle h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) k = case eb of
  Inl0 (NoOp6 a) -> eval6_7 (inj0 $ subst6 retP a retB) k
  Inl0 (Op6 eff' op vo x_op) ->
    if eff == eff'
      then eval6_7 (inj0 $ substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
      else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
    where
      (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
  Inl0 (Scope6 eff' scp vs recP recB x_op) ->
    if eff == eff'
      then eval6_7 (inj0 $ substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
      else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
    where
      (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
  Inr0 eb' -> eval6_7 eb' $ \case
    Inl0 (NoOp6 a) -> eval6_7 (inj0 $ subst6 retP a retB) k
    Inl0 (Op6 eff' op vo x_op) ->
      if eff == eff'
        then eval6_7 (inj0 $ substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
        else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
      where
        (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
    Inl0 (Scope6 eff' scp vs recP recB x_op) ->
      if eff == eff'
        then eval6_7 (inj0 $ substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
        else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
      where
        (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
    Inr0 eb'' -> k (inj0 $ Handle6 h eb'')
--
apply6_7 (Cont7If ei ee ec) k = case ec of
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_7 (inj0 ei) k
      else eval6_7 (inj0 ee) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> If6 t ei ee) . x_op)
  Inr0 ec' -> eval6_7 ec' $ \case
    Inl0 (NoOp6 (BoolV6 c)) ->
      if c
        then eval6_7 (inj0 ei) k
        else eval6_7 (inj0 ee) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> If6 t ei ee) . x_op)
    Inr0 ec'' -> k (inj0 $ If6 ec'' ei ee)
apply6_7 (Cont7App1 ea ef) k = case ef of
  Inl0 (NoOp6 (LambdaV6 param f)) -> apply6_7 (Cont7App2 param f (inj0 ea)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 t ea) . x_op)
  Inr0 e1' -> eval6_7 e1' $ \case
    Inl0 (NoOp6 (LambdaV6 param f)) -> apply6_7 (Cont7App2 param f (inj0 ea)) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 t ea) . x_op)
    Inr0 e1'' -> k (inj0 $ App6 e1'' ea)
apply6_7 (Cont7App2 param f ea) k = case ea of
  Inl0 (NoOp6 va) -> eval6_7 (inj0 $ subst6 param va f) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
  Inr0 e2' -> eval6_7 e2' $ \case
    Inl0 (NoOp6 va) -> eval6_7 (inj0 $ subst6 param va f) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
    Inr0 e2'' -> k (inj0 $ App6 (Lit6 $ LambdaV6 param f) e2'')
apply6_7 (Cont7Pair1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_7 (Cont7Pair2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 t e2) . x_op)
  Inr0 e1' -> eval6_7 e1' $ \case
    Inl0 (NoOp6 v1) -> apply6_7 (Cont7Pair2 v1 (inj0 e2)) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 t e2) . x_op)
    Inr0 e1'' -> k (inj0 $ Pair6 e1'' e2)
apply6_7 (Cont7Pair2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
  Inr0 e2' -> eval6_7 e2' $ \case
    Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
    Inr0 e2'' -> k (inj0 $ Pair6 (Lit6 v1) e2'')
apply6_7 (Cont7Cons1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_7 (Cont7Cons2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 t e2) . x_op)
  Inr0 e1' -> eval6_7 e1' $ \case
    Inl0 (NoOp6 v1) -> apply6_7 (Cont7Cons2 v1 (inj0 e2)) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 t e2) . x_op)
    Inr0 e1'' -> k (inj0 $ Cons6 e1'' e2)
apply6_7 (Cont7Cons2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
  Inr0 e2' -> eval6_7 e2' $ \case
    Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
    Inr0 e2'' -> k (inj0 $ Cons6 (Lit6 v1) e2'')
apply6_7 (Cont7UnOp uop ex) k = case ex of
  Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> UnOp6 uop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> UnOp6 uop t) . x_op)
  Inr0 ex' -> eval6_7 ex' $ \case
    Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> UnOp6 uop t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> UnOp6 uop t) . x_op)
    Inr0 ex'' -> k (inj0 $ UnOp6 uop ex'')
apply6_7 (Cont7BinOp1 bop ey ex) k = case ex of
  Inl0 (NoOp6 vx) -> apply6_7 (Cont7BinOp2 vx bop (inj0 ey)) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 t bop ey) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 t bop ey) . x_op)
  Inr0 ex' -> eval6_7 ex' $ \case
    Inl0 (NoOp6 vx) -> apply6_7 (Cont7BinOp2 vx bop (inj0 ey)) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 t bop ey) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 t bop ey) . x_op)
    Inr0 ex'' -> k (inj0 $ BinOp6 ex'' bop ey)
apply6_7 (Cont7BinOp2 vx bop ey) k = case ey of
  Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
  Inr0 ey' -> eval6_7 ey' $ \case
    Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
    Inr0 ey'' -> k (inj0 $ BinOp6 (Lit6 vx) bop ey'')
--
apply6_7 (Cont7UnSum fl@(x, ex) fr@(y, ey) e) k = case e of
  Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_7 (subst6 x v ex) k
  Inl0 (NoOp6 (SumRightV6 v)) -> eval6_7 (subst6 y v ey) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
  Inr0 e' -> eval6_7 e' $ \case
    Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_7 (subst6 x v ex) k
    Inl0 (NoOp6 (SumRightV6 v)) -> eval6_7 (subst6 y v ey) k
    Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
    Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
    Inr0 e'' -> k (inj0 $ UnSum6 e'' fl fr)
apply6_7 (Cont7UnList en fc@(x, y, ec) e) k = case e of
  Inl0 (NoOp6 NilV6) -> eval6_7 en k
  Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_7 (substAll6 [(x, v), (y, vs)] ec) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
  Inr0 e' -> eval6_7 e' $ \case
    Inl0 (NoOp6 NilV6) -> eval6_7 en k
    Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_7 (substAll6 [(x, v), (y, vs)] ec) k
    Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
    Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
    Inr0 e'' -> k (inj0 $ UnList6 e'' en fc)

eval6_7 :: Expr6 -> (K7 -> a) -> a
eval6_7 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_7 (Closed6 a) k = k $ inj0 $ NoOp6 a
eval6_7 (Lit6 a) k = k $ inj0 $ NoOp6 a
eval6_7 (OpCall6 eff op ea) k = apply6_7 (Cont7OpCall eff op (inj0 ea)) k
eval6_7 (ScopeCall6 eff scp ea recP recB) k = apply6_7 (Cont7ScopeCall eff scp recP recB (inj0 ea)) k
eval6_7 (Let6 xA xP xB) k = apply6_7 (Cont7Let xP xB (inj0 xA)) k
eval6_7 (Handle6 h eb) k = apply6_7 (Cont7Handle h (inj0 eb)) k
--
eval6_7 (If6 ec ei ee) k = apply6_7 (Cont7If ei ee (inj0 ec)) k
eval6_7 (App6 ef ea) k = apply6_7 (Cont7App1 ea (inj0 ef)) k
eval6_7 (Pair6 e1 e2) k = apply6_7 (Cont7Pair1 e2 (inj0 e1)) k
eval6_7 Nil6 k = k $ inj0 $ NoOp6 NilV6
eval6_7 (Cons6 e1 e2) k = apply6_7 (Cont7Cons1 e2 (inj0 e1)) k
eval6_7 (UnOp6 uop ex) k = apply6_7 (Cont7UnOp uop (inj0 ex)) k
eval6_7 (BinOp6 ex bop ey) k = apply6_7 (Cont7BinOp1 bop ey (inj0 ex)) k
--
eval6_7 (UnSum6 e fl fr) k = apply6_7 (Cont7UnSum fl fr (inj0 e)) k
eval6_7 (UnList6 e en fc) k = apply6_7 (Cont7UnList en fc (inj0 e)) k

normalise6_7 :: Expr6 -> Result6
normalise6_7 e = eval6_7 (inj0 e) k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_7 e' k

---------------------------------------------------------------
---- Step 6.8. Inlining and simplification
---------------------------------------------------------------
type K8 = Result6 :+: Expr6

eval6_8 :: Expr6 -> (K8 -> a) -> a
eval6_8 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_8 (Closed6 a) k = k $ inj0 $ NoOp6 a
eval6_8 (Lit6 a) k = k $ inj0 $ NoOp6 a
eval6_8 (OpCall6 eff op ea) k = eval6_8 ea $ \case
    Inl0 (NoOp6 va) -> k $ inj0 $ Op6 eff op va id
    Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op (x_op t))
    Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op (x_op t))
    Inr0 ea' -> k (inj0 $ OpCall6 eff op ea')
eval6_8 (ScopeCall6 eff scp ea recP recB) k = eval6_8 ea $ \case
    Inl0 (NoOp6 va) -> k $ inj0 $ Scope6 eff scp va recP recB id
    Inl0 (Op6 eff' op' vo' x_op) -> k $ inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
    Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> k $ inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
    Inr0 ea' -> k (inj0 $ ScopeCall6 eff scp ea' recP recB)
eval6_8 (Let6 xA xP xB) k = eval6_8 xA $ \case
  Inl0 (NoOp6 xv) -> eval6_8 (inj0 $ subst6 xP xv xB) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
  Inr0 xA' -> k (inj0 $ Let6 xA' xP xB)
eval6_8 (Handle6 h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) k = eval6_8 eb $ \case
  Inl0 (NoOp6 a) -> eval6_8 (inj0 $ subst6 retP a retB) k
  Inl0 (Op6 eff' op vo x_op) ->
    if eff == eff'
      then eval6_8 (inj0 $ substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody) k
      else k $ inj0 $ Op6 eff' op vo (Handle6 h . x_op)
    where
      (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
  Inl0 (Scope6 eff' scp vs recP recB x_op) ->
    if eff == eff'
      then eval6_8 (inj0 $ substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB) k
      else k $ inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
    where
      (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
  Inr0 eb' -> k (inj0 $ Handle6 h eb')
--
eval6_8 (If6 ec ei ee) k = eval6_8 ec $ \case
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_8 (inj0 ei) k
      else eval6_8 (inj0 ee) k
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> If6 t ei ee) . x_op)
  Inr0 ec' -> k (inj0 $ If6 ec' ei ee)
eval6_8 (App6 e1 e2) k = eval6_8 e1 $ \case
  Inl0 (NoOp6 (LambdaV6 param f)) -> eval6_8 e2 $ \case
    Inl0 (NoOp6 va) -> eval6_8 (inj0 $ subst6 param va f) k
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
    Inr0 e2' -> k (inj0 $ App6 (Lit6 $ LambdaV6 param f) e2')
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> App6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> App6 t e2) . x_op)
  Inr0 e1' -> k (inj0 $ App6 e1' e2)
eval6_8 (Pair6 e1 e2) k = eval6_8 e1 $ \case
  Inl0 (NoOp6 v1) -> eval6_8 e2 $ \case
    Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (PairV6 v1 v2)
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
    Inr0 e2' -> k (inj0 $ Pair6 (Lit6 v1) e2')
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 t e2) . x_op)
  Inr0 e1' -> k (inj0 $ Pair6 e1' e2)
eval6_8 Nil6 k = k $ inj0 $ NoOp6 NilV6
eval6_8 (Cons6 e1 e2) k = eval6_8 e1 $ \case
  Inl0 (NoOp6 v1) -> eval6_8 e2 $ \case
    Inl0 (NoOp6 v2) -> k $ inj0 $ NoOp6 (ConsV6 v1 v2)
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
    Inr0 e2' -> k (inj0 $ Cons6 (Lit6 v1) e2')
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 t e2) . x_op)
  Inr0 e1' -> k (inj0 $ Cons6 e1' e2)
eval6_8 (UnOp6 uop ex) k = eval6_8 ex $ \case
  Inl0 (NoOp6 vx) -> k $ inj0 $ NoOp6 $ applyUnOp6 uop vx
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> UnOp6 uop t) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> UnOp6 uop t) . x_op)
  Inr0 ex' -> k (inj0 $ UnOp6 uop ex')
eval6_8 (BinOp6 ex bop ey) k = eval6_8 ex $ \case
  Inl0 (NoOp6 vx) -> eval6_8 ey $ \case
    Inl0 (NoOp6 vy) -> k $ inj0 $ NoOp6 $ applyBinOp6 vx bop vy
    Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
    Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
    Inr0 ey' -> k (inj0 $ BinOp6 (Lit6 vx) bop ey')
  Inl0 (Op6 eff op va x_op) -> k $ inj0 $ Op6 eff op va ((\t -> BinOp6 t bop ey) . x_op)
  Inl0 (Scope6 eff scp va recP recB x_op) -> k $ inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 t bop ey) . x_op)
  Inr0 ex' -> k (inj0 $ BinOp6 ex' bop ey)
--
eval6_8 (UnSum6 e fl@(x, ex) fr@(y, ey)) k = eval6_8 e $ \case
  Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_8 (subst6 x v ex) k
  Inl0 (NoOp6 (SumRightV6 v)) -> eval6_8 (subst6 y v ey) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
  Inr0 e' -> k (inj0 $ UnSum6 e' fl fr)
eval6_8 (UnList6 e en fc@(x, y, ec)) k = eval6_8 e $ \case
  Inl0 (NoOp6 NilV6) -> eval6_8 en k
  Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_8 (substAll6 [(x, v), (y, vs)] ec) k
  Inl0 (Op6 eff op vo x_op) -> k $ inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
  Inl0 (Scope6 eff scp vs recP recB x_op) -> k $ inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
  Inr0 e' -> k (inj0 $ UnList6 e' en fc)

normalise6_8 :: Expr6 -> Result6
normalise6_8 e = eval6_8 (inj0 e) k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_8 e' k

---------------------------------------------------------------
---- Step 6.9. Back to Direct Style
---------------------------------------------------------------
eval6_9 :: Expr6 -> (Result6 :+: Expr6)
eval6_9 e = go e
  where
    go (Var6 nm) = error ("Free variable: " <> nm)
    go (Closed6 a) = inj0 $ NoOp6 a
    go (Lit6 a) = inj0 $ NoOp6 a
    go (OpCall6 eff op ea) = case eval6_9 ea of
        Inl0 (NoOp6 va) -> inj0 $ Op6 eff op va id
        Inl0 (Op6 eff' op' vo' x_op) -> inj0 $ Op6 eff' op' vo' (\t -> OpCall6 eff op (x_op t))
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> OpCall6 eff op (x_op t))
        Inr0 ea' -> inj0 $ OpCall6 eff op ea'
    go (ScopeCall6 eff scp ea recP recB) = case eval6_9 ea of
        Inl0 (NoOp6 va) -> inj0 $ Scope6 eff scp va recP recB id
        Inl0 (Op6 eff' op' vo' x_op) -> inj0 $ Op6 eff' op' vo' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
        Inl0 (Scope6 eff' scp' vs' recP' recB' x_op) -> inj0 $ Scope6 eff' scp' vs' recP' recB' (\t -> ScopeCall6 eff scp (x_op t) recP recB)
        Inr0 ea' -> inj0 $ ScopeCall6 eff scp ea' recP recB
    go (Let6 xA xP xB) = case eval6_9 xA of
      Inl0 (NoOp6 xv) -> eval6_9 (inj0 $ subst6 xP xv xB)
      Inl0 (Op6 eff op vo x_op) -> inj0 $ Op6 eff op vo (\t -> Let6 (x_op t) xP xB)
      Inl0 (Scope6 eff scp vs recP recB x_op) -> inj0 $ Scope6 eff scp vs recP recB (\t -> Let6 (x_op t) xP xB)
      Inr0 xA' -> inj0 $ Let6 xA' xP xB
    go (Handle6 h@(Handler6 eff (retP, retB) ops scps (mendP, mendB)) eb) = case eval6_9 eb of
      Inl0 (NoOp6 a) -> eval6_9 (inj0 $ subst6 retP a retB)
      Inl0 (Op6 eff' op vo x_op) ->
        if eff == eff'
          then eval6_9 (inj0 $ substAll6 [(opParamP, vo), ("resume", resumption6 h x_op)] opBody)
          else inj0 $ Op6 eff' op vo (Handle6 h . x_op)
        where
          (_, opParamP, opBody) = fromJust $ find (\(op', _, _) -> op == op') ops
      Inl0 (Scope6 eff' scp vs recP recB x_op) ->
        if eff == eff'
          then eval6_9 (inj0 $ substAll6 [(scpParamP, vs), (scpRecP, LambdaV6 recP (Handle6 h recB)), ("resume", resumption6 h x_op)] scpB)
          else inj0 $ Scope6 eff' scp vs recP (Handle6 h recB) (\fx -> Let6 fx mendP (subst6 "resume" (resumption6 h x_op) mendB))
        where
          (_, scpParamP, scpRecP, scpB) = fromJust $ find (\(scp', _, _, _) -> scp == scp') scps
      Inr0 eb' -> inj0 $ Handle6 h eb'
    --
    go (If6 ec ei ee) = case eval6_9 ec of
      Inl0 (NoOp6 (BoolV6 c)) ->
        if c
          then eval6_9 (inj0 ei)
          else eval6_9 (inj0 ee)
      Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
      Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> If6 t ei ee) . x_op)
      Inr0 ec' -> inj0 $ If6 ec' ei ee
    go (App6 e1 e2) = case eval6_9 e1 of
      Inl0 (NoOp6 (LambdaV6 param f)) -> case eval6_9 e2 of
        Inl0 (NoOp6 va) -> eval6_9 (inj0 $ subst6 param va f)
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
        Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
        Inr0 e2' -> inj0 $ App6 (Lit6 $ LambdaV6 param f) e2'
      Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> App6 t e2) . x_op)
      Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> App6 t e2) . x_op)
      Inr0 e1' -> inj0 $ App6 e1' e2
    go (Pair6 e1 e2) = case eval6_9 e1 of
      Inl0 (NoOp6 v1) -> case eval6_9 e2 of
        Inl0 (NoOp6 v2) -> inj0 $ NoOp6 (PairV6 v1 v2)
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
        Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 (Lit6 v1) t) . x_op)
        Inr0 e2' -> inj0 $ Pair6 (Lit6 v1) e2'
      Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
      Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> Pair6 t e2) . x_op)
      Inr0 e1' -> inj0 $ Pair6 e1' e2
    go Nil6 = inj0 $ NoOp6 NilV6
    go (Cons6 e1 e2) = case eval6_9 e1 of
      Inl0 (NoOp6 v1) -> case eval6_9 e2 of
        Inl0 (NoOp6 v2) -> inj0 $ NoOp6 (ConsV6 v1 v2)
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
        Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 (Lit6 v1) t) . x_op)
        Inr0 e2' -> inj0 $ Cons6 (Lit6 v1) e2'
      Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
      Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> Cons6 t e2) . x_op)
      Inr0 e1' -> inj0 $ Cons6 e1' e2
    go (UnOp6 uop ex) = case eval6_9 ex of
      Inl0 (NoOp6 vx) -> inj0 $ NoOp6 $ applyUnOp6 uop vx
      Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> UnOp6 uop t) . x_op)
      Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> UnOp6 uop t) . x_op)
      Inr0 ex' -> inj0 $ UnOp6 uop ex'
    go (BinOp6 ex bop ey) = case eval6_9 ex of
      Inl0 (NoOp6 vx) -> case eval6_9 ey of
        Inl0 (NoOp6 vy) -> inj0 $ NoOp6 $ applyBinOp6 vx bop vy
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
        Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 (Lit6 vx) bop t) . x_op)
        Inr0 ey' -> inj0 $ BinOp6 (Lit6 vx) bop ey'
      Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> BinOp6 t bop ey) . x_op)
      Inl0 (Scope6 eff scp va recP recB x_op) -> inj0 $ Scope6 eff scp va recP recB ((\t -> BinOp6 t bop ey) . x_op)
      Inr0 ex' -> inj0 $ BinOp6 ex' bop ey
    --
    go (UnSum6 e fl@(x, ex) fr@(y, ey)) = case eval6_9 e of
      Inl0 (NoOp6 (SumLeftV6 v)) -> eval6_9 (subst6 x v ex)
      Inl0 (NoOp6 (SumRightV6 v)) -> eval6_9 (subst6 y v ey)
      Inl0 (Op6 eff op vo x_op) -> inj0 $ Op6 eff op vo ((\t -> UnSum6 t fl fr) . x_op)
      Inl0 (Scope6 eff scp vs recP recB x_op) -> inj0 $ Scope6 eff scp vs recP recB ((\t -> UnSum6 t fl fr) . x_op)
      Inr0 e' -> inj0 $ UnSum6 e' fl fr
    go (UnList6 e en fc@(x, y, ec)) = case eval6_9 e of
      Inl0 (NoOp6 NilV6) -> eval6_9 en
      Inl0 (NoOp6 (ConsV6 v vs)) -> eval6_9 (substAll6 [(x, v), (y, vs)] ec)
      Inl0 (Op6 eff op vo x_op) -> inj0 $ Op6 eff op vo ((\t -> UnList6 t en fc) . x_op)
      Inl0 (Scope6 eff scp vs recP recB x_op) -> inj0 $ Scope6 eff scp vs recP recB ((\t -> UnList6 t en fc) . x_op)
      Inr0 e' -> inj0 $ UnList6 e' en fc

normalise6_9 :: Expr6 -> Result6
normalise6_9 e = case eval6_9 (inj0 e) of
  Inl0 v -> v
  Inr0 e' -> error ("STUCK: " <> show e')
