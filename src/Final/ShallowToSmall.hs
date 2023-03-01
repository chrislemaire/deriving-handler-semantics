{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Final.ShallowToSmall where

import Control.Monad (ap, join, liftM2, (>=>))
import Control.Monad.Writer (liftM)
import Data.List (find)
import Data.Maybe (fromJust)
import Final.DTC

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
  Impure op k >>= f = Impure op (\v -> k v >>= f)
  
data Result0 sig a where
  NoOp0 :: a -> Result0 sig a
  Op0 :: sig x -> (x -> Freer sig a) -> Result0 sig a

eval0 :: Freer sig a -> Result0 sig a
eval0 (Pure v) = NoOp0 v
eval0 (Impure op k) = Op0 op k

data EPure a

run0 :: Freer EPure a -> a
run0 (Pure a) = a



data St st a where
  Get :: () -> St st st
  Put :: st -> St st ()

hSt0 :: Freer (St st :++: r) a -> Freer r (st -> Freer r (st, a))
hSt0 (Pure a) = Pure (\st -> return (st, a))
hSt0 (Impure (Inl (Get ())) k) = Pure (\st -> hSt0 (k st) >>= ($ st))
hSt0 (Impure (Inl (Put st)) k) = Pure (\_ -> hSt0 (k ()) >>= ($ st))
hSt0 (Impure (Inr op) k) = Impure op (hSt0 . k)

---------------------------------------------------------------
---- 0 - Abstract handlers from usage
---------------------------------------------------------------
-- Deep handlers
data DHandler0 eff r a w where
  DHandler0 ::
    (forall x. eff x -> (x -> Freer r w) -> Freer r w) ->
    (a -> Freer r w) ->
    DHandler0 eff r a w

dHandle0 :: DHandler0 eff r a w -> Freer (eff :++: r) a -> Freer r w
dHandle0 hlr@(DHandler0 ops ret) (Pure a) = ret a
dHandle0 hlr@(DHandler0 ops ret) (Impure (Inl op) k) = ops op (dHandle0 hlr . k)
dHandle0 hlr@(DHandler0 ops ret) (Impure (Inr op) k) = Impure op (dHandle0 hlr . k)

hStD0' :: Freer (St st :++: r) a -> Freer r (st -> Freer r (st, a))
hStD0' =
  dHandle0
    ( DHandler0
        ( \op k -> case op of
            Get () -> return $ \st -> join (k st <*> return st)
            Put st -> return $ \_ -> join (k () <*> return st)
        )
        (\a -> return (\st -> return (st, a)))
    )

-- But, we want Shallow handlers instead.
data SHandler0 eff r a w where
  SHandler0 ::
       (forall x. eff x 
          -> (x -> Freer (eff :++: r) a)
          -> (Freer (eff :++: r) a -> Freer r w)
          -> Freer r w)
    -> (a -> Freer r w)
    -> SHandler0 eff r a w

sHandle0 :: SHandler0 eff r a w
         -> Freer r (Freer (eff :++: r) a)
         -> Freer r w
sHandle0 hlr@(SHandler0 ops ret) seb =
  seb >>= \case
    Pure a -> ret a
    Impure (Inl op) k -> 
      ops op k (sHandle0 hlr . return)
    Impure (Inr op) k ->
      Impure op (sHandle0 hlr . return . k)

--hSt0' :: Freer (St st :++: r) a -> Freer r (st -> Freer r (st, a))
--hSt0' =
--  sHandle0
--    ( SHandler0
--        ( \op k hdl -> case op of
--            Get () -> Pure (\st -> hdl (k st) >>= ($ st))
--            Put st -> Pure (\_ -> hdl (k ()) >>= ($ st))
--        )
--        (\a -> return (\st -> return (st, a)))
--    )

opCall0 :: eff :<<: sig => (x -> eff a) -> Freer sig x -> Freer sig a
opCall0 eff xt = xt >>= \x -> Impure (inj $ eff x) return

let0 :: Freer sig x -> (x -> Freer sig a) -> Freer sig a
let0 x f = x >>= f

cons0 :: Freer sig a -> Freer sig [a] -> Freer sig [a]
cons0 = liftM2 (:)

app0 :: Freer sig (x -> Freer sig a) -> Freer sig x -> Freer sig a
app0 ef ea = do
  body <- ef
  a <- ea
  body a

pair0 :: Freer sig x -> Freer sig y -> Freer sig (x, y)
pair0 = liftM2 (,)

unOp0 :: (x -> a) -> Freer sig x -> Freer sig a
unOp0 uop ex = uop <$> ex

binOp0 :: Freer sig x -> (x -> y -> a) -> Freer sig y -> Freer sig a
binOp0 ex bop = liftM2 bop ex

if0 :: Freer sig Bool -> Freer sig a -> Freer sig a -> Freer sig a
if0 ec ei ee = ec >>= \c -> if c then ei else ee

data Local6Eff1 a where
  Local6Eff1Op1 :: Int -> Local6Eff1 Int

exp0 :: Freer EPure Int
exp0 =
  sHandle0
    ( SHandler0
        ( \op resume hdl -> case op of
            Local6Eff1Op1 v0 -> hdl (resume v0)
        )
        (\v0 -> return v0)
    )
    (return $ (+) <$> opCall0 Local6Eff1Op1 (return 86) <*> opCall0 Local6Eff1Op1 (return (-102)))

---------------------------------------------------------------
---- 1 - Split Impure into Let and OpCall
---------------------------------------------------------------
data Suspended a = Suspended {unSuspend :: a}
  deriving (Show, Eq)

suspend :: a -> Suspended a
suspend = Suspended

data Expr1 sig a where
  Lit1 :: a -> Expr1 sig a
  OpCall1 :: sig a -> Expr1 sig a
  Let1 :: Expr1 sig x -> (x -> Expr1 sig a) -> Expr1 sig a

instance Functor (Expr1 sig) where
  fmap = liftM

instance Applicative (Expr1 sig) where
  pure = Lit1
  (<*>) = ap

instance Monad (Expr1 sig) where
  return = pure
  Lit1 a >>= f = f a
  OpCall1 op >>= f = Let1 (OpCall1 op) f
  Let1 arg body >>= f = Let1 arg (\v -> body v >>= f)

op1 :: sig x -> (x -> Expr1 sig a) -> Expr1 sig a
op1 op = Let1 (OpCall1 op)

opCall1 :: eff :<<: sig => (x -> eff a) -> Expr1 sig x -> Expr1 sig a
opCall1 eff xt = xt >>= \x -> OpCall1 (inj $ eff x)

data SHandler1 eff r a w where
  SHandler1 ::
    (forall x. eff x -> (x -> Expr1 (eff :++: r) a) -> (Suspended (Expr1 (eff :++: r) a) -> Expr1 r w) -> Expr1 r w) ->
    (a -> Expr1 r w) ->
    SHandler1 eff r a w

sHandle1 :: SHandler1 eff r a w -> Expr1 r (Suspended (Expr1 (eff :++: r) a)) -> Expr1 r w
sHandle1 hlr@(SHandler1 ops ret) fb =
  fb >>= \eb -> case unSuspend eb of
    Lit1 a -> ret a
    Let1 (OpCall1 (Inl op)) k -> ops op k (\x -> sHandle1 hlr (return x))
    Let1 (OpCall1 (Inr op)) k -> op1 op (sHandle1 hlr . return . suspend . k)
    Let1 arg body -> sHandle1 hlr (return $ suspend $ arg >>= body)
    OpCall1 op -> sHandle1 hlr (return $ suspend $ op1 op Lit1)

data Result1 sig a where
  NoOp1 :: a -> Result1 sig a
  Op1 :: sig x -> (x -> Expr1 sig a) -> Result1 sig a

run1 :: Expr1 EPure a -> a
run1 e = case eval1 e of
  NoOp1 v -> v

eval1 :: Expr1 sig a -> Result1 sig a
eval1 (Lit1 v) = NoOp1 v
eval1 (OpCall1 op) = Op1 op return
eval1 (Let1 ev body) = case eval1 ev of
  NoOp1 v -> eval1 (body v)
  Op1 op k -> Op1 op (\t -> k t >>= body)

cons1 :: Expr1 sig a -> Expr1 sig [a] -> Expr1 sig [a]
cons1 = liftM2 (:)

app1 :: Expr1 sig (x -> Expr1 sig a) -> Expr1 sig x -> Expr1 sig a
app1 ef ea = do
  body <- ef
  a <- ea
  body a

pair1 :: Expr1 sig x -> Expr1 sig y -> Expr1 sig (x, y)
pair1 = liftM2 (,)

unOp1 :: (x -> a) -> Expr1 sig x -> Expr1 sig a
unOp1 uop ex = uop <$> ex

binOp1 :: Expr1 sig x -> (x -> y -> a) -> Expr1 sig y -> Expr1 sig a
binOp1 ex bop = liftM2 bop ex

if1 :: Expr1 sig Bool -> Expr1 sig a -> Expr1 sig a -> Expr1 sig a
if1 ec ei ee = ec >>= \c -> if c then ei else ee

exp1 :: Expr1 EPure Int
exp1 =
  sHandle1
    ( SHandler1
        ( \op resume hdl -> case op of
            Local6Eff1Op1 v0 -> hdl (suspend $ resume v0)
        )
        (\v0 -> return v0)
    )
    (return $ suspend $ (+) <$> opCall1 Local6Eff1Op1 (return 86) <*> opCall1 Local6Eff1Op1 (return (-102)))

---------------------------------------------------------------
---- 2 - Lift Handle into Expr
---------------------------------------------------------------
data SHandler2 eff r a w where
  SHandler2 ::
    (forall x. eff x -> (x -> Expr2 (eff :++: r) a) -> (Suspended (Expr2 (eff :++: r) a) -> Expr2 r w) -> Expr2 r w) ->
    (a -> Expr2 r w) ->
    SHandler2 eff r a w

data Expr2 sig a where
  Lit2 :: a -> Expr2 sig a
  OpCall2 :: sig a -> Expr2 sig a
  Let2 :: Expr2 sig x -> (x -> Expr2 sig a) -> Expr2 sig a
  SHandle2 :: SHandler2 eff r a w -> Expr2 r (Suspended (Expr2 (eff :++: r) a)) -> Expr2 r w

instance Functor (Expr2 sig) where
  fmap = liftM

instance Applicative (Expr2 sig) where
  pure = Lit2
  (<*>) = ap

instance Monad (Expr2 sig) where
  return = pure
  Lit2 a >>= f = f a
  Let2 arg k >>= f = Let2 arg (k >=> f)
  e >>= f = Let2 e f

data Result2 sig a where
  NoOp2 :: a -> Result2 sig a
  Op2 :: sig x -> (x -> Expr2 sig a) -> Result2 sig a

op2 :: sig x -> (x -> Expr2 sig a) -> Expr2 sig a
op2 op = Let2 (OpCall2 op)

opCall2 :: eff :<<: sig => (x -> eff a) -> Expr2 sig x -> Expr2 sig a
opCall2 eff xt = xt >>= \x -> OpCall2 (inj $ eff x)

eval2 :: Expr2 sig a -> Result2 sig a
eval2 (Lit2 v) = NoOp2 v
eval2 (OpCall2 op) = Op2 op Lit2
eval2 (Let2 ev body) = case eval2 ev of
  NoOp2 v -> eval2 (body v)
  Op2 op k -> Op2 op (k >=> body) -- Case added to re-connect op-continuation and let body
  -- obtained by transforming let0
eval2 (SHandle2 hlr@(SHandler2 ops ret) seb) = case eval2 seb of
  NoOp2 eb ->
    case eval2 (unSuspend eb) of
      NoOp2 v -> eval2 (ret v)
      Op2 (Inl op) k -> eval2 (ops op k (SHandle2 hlr . return))
      Op2 (Inr op) k -> Op2 op (SHandle2 hlr . return . suspend . k)
  Op2 op k -> Op2 op (SHandle2 hlr . k)

run2 :: Expr2 EPure a -> a
run2 e = case eval2 e of
  NoOp2 v -> v

exp2 :: Expr2 EPure Int
exp2 =
  SHandle2
    ( SHandler2
        ( \op resume hdl -> case op of
            Local6Eff1Op1 v0 -> hdl (suspend $ resume v0)
        )
        (\v0 -> return v0)
    )
    (return $ suspend $ binOp2 (opCall2 Local6Eff1Op1 (return 86)) Add2 (opCall2 Local6Eff1Op1 (return (-102))))

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

pair2 :: Expr2 sig x -> Expr2 sig y -> Expr2 sig (x, y)
pair2 = liftM2 (,)

pair2_1 :: Expr2 sig x -> Expr2 sig y -> Expr2 sig (x, y)
pair2_1 e1 e2 = do
  v1 <- e1
  v2 <- e2
  return (v1, v2)

pair2_2 :: Expr2 sig x -> Expr2 sig y -> Expr2 sig (x, y)
pair2_2 e1 e2 =
  e1 >>= \v1 ->
    e2 >>= \v2 ->
      return (v1, v2)

pair2_3 :: Expr2 sig x -> Expr2 sig y -> Expr2 sig (x, y)
pair2_3 e1 e2 =
  Let2
    e1
    ( \v1 ->
        Let2
          e2
          ( \v2 ->
              Lit2 (v1, v2)
          )
    )

unOp2 :: UnOpOperator2 x a -> Expr2 sig x -> Expr2 sig a
unOp2 unOp ex = do
  vx <- ex
  return
    ( ( case unOp of
          Fst2 -> fst
          Snd2 -> snd
      )
        vx
    )

binOp2 :: Expr2 sig x -> BinOpOperator2 x y a -> Expr2 sig y -> Expr2 sig a
binOp2 ex binOp ey = do
  vx <- ex
  vy <- ey
  return
    ( ( case binOp of
          Add2 -> (+)
          Mul2 -> (*)
          Concat2 -> (<>)
      )
        vx
        vy
    )

cons2 :: Expr2 sig a -> Expr2 sig [a] -> Expr2 sig [a]
cons2 x xs = do
  vx <- x
  vxs <- xs
  return (vx : vxs)

list2 :: [Expr2 sig a] -> Expr2 sig [a]
list2 [] = return []
list2 (x : xs) = do
  vx <- x
  vxs <- list2 xs
  return (vx : vxs)

app2 :: Expr2 sig (x -> Expr2 sig a) -> Expr2 sig x -> Expr2 sig a
app2 ef ea = do
  vf <- ef
  va <- ea
  vf va

if2 :: Expr2 sig Bool -> Expr2 sig a -> Expr2 sig a -> Expr2 sig a
if2 c t e = do
  vc <- c
  if vc
    then t
    else e

---------------------------------------------------------------
---- 3.2 - Encode those constructions with Values and additional Exprs
---------------------------------------------------------------
data Value3 a where
  LambdaV3 :: (Value3 x -> Expr3 sig a) -> Value3 (x -> Expr3 sig a)
  IntV3 :: Int -> Value3 Int
  BoolV3 :: Bool -> Value3 Bool
  UnitV3 :: Value3 ()
  PairV3 :: Value3 x -> Value3 y -> Value3 (x, y)
  NilV3 :: Value3 [a]
  ConsV3 :: Value3 a -> Value3 [a] -> Value3 [a]
  SuspendedV3 :: Suspended (Expr3 sig a) -> Value3 (Suspended (Expr3 sig a))

suspend3 :: Expr3 sig a -> Value3 (Suspended (Expr3 sig a))
suspend3 = SuspendedV3 . suspend

data UnOpOperator3 x a where
  Fst3 :: UnOpOperator3 (x, y) x
  Snd3 :: UnOpOperator3 (x, y) y

data BinOpOperator3 x y a where
  Concat3 :: BinOpOperator3 [a] [a] [a]
  Add3 :: BinOpOperator3 Int Int Int
  Mul3 :: BinOpOperator3 Int Int Int

data Expr3 sig a where
  Lit3 :: Value3 a -> Expr3 sig a
  OpCall3 :: sig a -> Expr3 sig a
  Let3 :: Expr3 sig x -> (Value3 x -> Expr3 sig a) -> Expr3 sig a
  SHandle3 :: SHandler3 eff r a w -> Expr3 r (Suspended (Expr3 (eff :++: r) a)) -> Expr3 r w
  App3 :: Expr3 sig (x -> Expr3 sig a) -> Expr3 sig x -> Expr3 sig a
  If3 :: Expr3 sig Bool -> Expr3 sig a -> Expr3 sig a -> Expr3 sig a
  Pair3 :: Expr3 sig x -> Expr3 sig y -> Expr3 sig (x, y)
  Nil3 :: Expr3 sig [a]
  Cons3 :: Expr3 sig a -> Expr3 sig [a] -> Expr3 sig [a]
  UnOp3 :: UnOpOperator3 x a -> Expr3 sig x -> Expr3 sig a
  BinOp3 :: Expr3 sig x -> BinOpOperator3 x y a -> Expr3 sig y -> Expr3 sig a

-- No more monad instance, because returning is now
-- impossible due to the limitation on value types (GADTs).

data SHandler3 eff r a w where
  SHandler3 ::
    (forall x. eff x -> (Value3 x -> Expr3 (eff :++: r) a) -> (Value3 (Suspended (Expr3 (eff :++: r) a)) -> Expr3 r w) -> Expr3 r w) ->
    (Value3 a -> Expr3 r w) ->
    SHandler3 eff r a w

-- Insert the result type for dealing with either
-- returning an incomplete op or a value.
data Result3 sig a where
  NoOp3 :: Value3 a -> Result3 sig a
  Op3 :: sig x -> (Value3 x -> Expr3 sig a) -> Result3 sig a

opCall3 :: eff :<<: sig => (Value3 x -> eff a) -> Expr3 sig x -> Expr3 sig a
opCall3 eff xt = Let3 xt (\x -> OpCall3 (inj $ eff x))

check_result3 ::
  Result3 sig x ->
  (Value3 x -> Result3 sig a) ->
  (Expr3 sig x -> Expr3 sig a) ->
  Result3 sig a
check_result3 (NoOp3 v) k _ = k v
check_result3 (Op3 op x_op) _ x_op' = Op3 op (x_op' . x_op)

concatListVs3 :: Value3 [a] -> Value3 [a] -> Value3 [a]
concatListVs3 NilV3 NilV3 = NilV3
concatListVs3 NilV3 vs' = vs'
concatListVs3 vs NilV3 = vs
concatListVs3 (ConsV3 v vs) vs' = ConsV3 v (concatListVs3 vs vs')

eval3 :: Expr3 sig a -> Result3 sig a
eval3 (Lit3 v) = NoOp3 v
eval3 (OpCall3 op) = Op3 op Lit3
eval3 (Let3 ev body) =
  case eval3 ev of
    NoOp3 v -> eval3 (body v)
    Op3 op x_op -> Op3 op ((\t -> Let3 t body) . x_op)
eval3 (SHandle3 hlr@(SHandler3 ops ret) seb) = case eval3 seb of
  NoOp3 (SuspendedV3 eb) ->
    case eval3 (unSuspend eb) of
      NoOp3 v -> eval3 (ret v)
      Op3 (Inl op) k -> eval3 (ops op k (SHandle3 hlr . Lit3))
      Op3 (Inr op) k -> Op3 op (SHandle3 hlr . Lit3 . suspend3 . k)
  Op3 op k -> Op3 op (SHandle3 hlr . k)
--
eval3 (If3 ec ei ee) =
  check_result3
    (eval3 ec)
    ( \(BoolV3 c) ->
        if c
          then eval3 ei
          else eval3 ee
    )
    (\t -> If3 t ei ee)
eval3 (App3 ef ea) =
  check_result3
    (eval3 ef)
    ( \vf@(LambdaV3 f) ->
        check_result3
          (eval3 ea)
          (\va -> eval3 (f va))
          (\t -> App3 (Lit3 vf) t)
    )
    (\t -> App3 t ea)
eval3 (Pair3 e1 e2) =
  --  eval3 (Let3 e1 (\v1 ->
  --           Let3 e2 (\v2 ->
  --             Lit3 (v1, v2))))
  case eval3 e1 of
    NoOp3 v1 ->
      case eval3 e2 of
        NoOp3 v2 -> NoOp3 (PairV3 v1 v2)
        Op3 op x_op -> Op3 op ((\t -> Pair3 (Lit3 v1) t) . x_op)
    Op3 op x_op -> Op3 op ((\t -> Pair3 t e2) . x_op)
eval3 Nil3 = NoOp3 NilV3
eval3 (Cons3 e1 e2) =
  check_result3
    (eval3 e1)
    ( \v1 ->
        check_result3
          (eval3 e2)
          (\v2 -> NoOp3 (ConsV3 v1 v2))
          (\t -> Cons3 (Lit3 v1) t)
    )
    (\t -> Cons3 t e2)
eval3 (UnOp3 unOp ex) =
  check_result3
    (eval3 ex)
    ( \vx ->
        NoOp3 $
          ( case unOp of
              Fst3 -> \(PairV3 x _) -> x
              Snd3 -> \(PairV3 _ x) -> x
          )
            vx
    )
    (\t -> UnOp3 unOp t)
eval3 (BinOp3 ex binOp ey) =
  check_result3
    (eval3 ex)
    ( \vx ->
        check_result3
          (eval3 ey)
          ( \vy ->
              NoOp3 $
                ( case binOp of
                    Add3 -> (\(IntV3 x) (IntV3 y) -> IntV3 (x + y))
                    Mul3 -> (\(IntV3 x) (IntV3 y) -> IntV3 (x * y))
                    Concat3 -> concatListVs3
                )
                  vx
                  vy
          )
          (\t -> BinOp3 (Lit3 vx) binOp t)
    )
    (\t -> BinOp3 t binOp ey)

run3 :: Expr3 EPure a -> Value3 a
run3 e = case eval3 e of
  NoOp3 v -> v

data Local3Eff1 a where
  Local3Eff1Op1 :: Value3 Int -> Local3Eff1 Int

exp3 :: Expr3 EPure Int
exp3 =
  SHandle3
    ( SHandler3
        ( \op resume hdl -> case op of
            Local3Eff1Op1 v0 -> hdl (suspend3 $ resume v0)
        )
        (\v0 -> Lit3 v0)
    )
    (Lit3 $ suspend3 $ BinOp3 (opCall3 Local3Eff1Op1 (Lit3 (IntV3 86))) Add3 (opCall3 Local3Eff1Op1 (Lit3 (IntV3 (-102)))))

---------------------------------------------------------------
---- 4 - (Optionally) Remove intrinsic typing
---------------------------------------------------------------
data Value4
  = LambdaV4 (Value4 -> Expr4)
  | IntV4 Int
  | BoolV4 Bool
  | UnitV4
  | PairV4 Value4 Value4
  | NilV4
  | ConsV4 Value4 Value4
  | SuspendedV4 (Suspended Expr4)

suspend4 :: Expr4 -> Value4
suspend4 = SuspendedV4 . suspend

data UnOpOperator4 = Fst4 | Snd4 deriving (Show, Eq)

data BinOpOperator4 = Add4 | Mul4 | Concat4 deriving (Show, Eq)

data Expr4
  = Lit4 Value4
  | OpCall4 String String Expr4
  | Let4 Expr4 (Value4 -> Expr4)
  | SHandle4 SHandler4 Expr4
  | If4 Expr4 Expr4 Expr4
  | App4 Expr4 Expr4
  | Pair4 Expr4 Expr4
  | Nil4
  | Cons4 Expr4 Expr4
  | UnOp4 UnOpOperator4 Expr4
  | BinOp4 Expr4 BinOpOperator4 Expr4

data SHandler4 where
  SHandler4 ::
    String ->
    (String -> Value4 -> (Value4 -> Expr4) -> (Value4 -> Expr4) -> Expr4) ->
    (Value4 -> Expr4) ->
    SHandler4

data Result4 where
  NoOp4 :: Value4 -> Result4
  Op4 :: String -> String -> Value4 -> (Value4 -> Expr4) -> Result4

check_result4 ::
  Result4 ->
  (Value4 -> Result4) ->
  (Expr4 -> Expr4) ->
  Result4
check_result4 (NoOp4 v) k _ = k v
check_result4 (Op4 eff op va x_op) _ x_op' = Op4 eff op va (x_op' . x_op)

eval4 :: Expr4 -> Result4
eval4 (Lit4 v) = NoOp4 v
eval4 (OpCall4 eff op ea) =
  check_result4
    (eval4 ea)
    (\v -> Op4 eff op v Lit4)
    (\t -> OpCall4 eff op t)
eval4 (Let4 ev body) =
  check_result4
    (eval4 ev)
    (\v -> eval4 (body v))
    (\t -> Let4 t body)
eval4 (SHandle4 hlr@(SHandler4 eff ops ret) seb) = case eval4 seb of
  NoOp4 (SuspendedV4 eb) ->
    case eval4 (unSuspend eb) of
      NoOp4 v -> eval4 (ret v)
      Op4 eff' op va k ->
        if eff == eff'
          then eval4 (ops op va k (SHandle4 hlr . Lit4))
          else Op4 eff' op va (SHandle4 hlr . Lit4 . suspend4 . k)
  Op4 eff' op va k -> Op4 eff' op va (SHandle4 hlr . k)
--
eval4 (If4 ec ei ee) =
  check_result4
    (eval4 ec)
    ( \(BoolV4 c) ->
        if c
          then eval4 ei
          else eval4 ee
    )
    (\t -> If4 t ei ee)
eval4 (App4 ef ea) =
  check_result4
    (eval4 ef)
    ( \vf@(LambdaV4 f) ->
        check_result4
          (eval4 ea)
          (\va -> eval4 (f va))
          (\t -> App4 (Lit4 vf) t)
    )
    (\t -> App4 t ea)
eval4 (Pair4 e1 e2) =
  check_result4
    (eval4 e1)
    ( \v1 ->
        check_result4
          (eval4 e2)
          (\v2 -> NoOp4 (PairV4 v1 v2))
          (\t -> Pair4 (Lit4 v1) t)
    )
    (\t -> Pair4 t e2)
eval4 Nil4 = NoOp4 NilV4
eval4 (Cons4 e1 e2) =
  check_result4
    (eval4 e1)
    ( \v1 ->
        check_result4
          (eval4 e2)
          (\v2 -> NoOp4 (ConsV4 v1 v2))
          (\t -> Cons4 (Lit4 v1) t)
    )
    (\t -> Cons4 t e2)
eval4 (UnOp4 unOp ex) =
  check_result4
    (eval4 ex)
    (\vx -> applyUnOp4 unOp vx)
    (\t -> UnOp4 unOp t)
eval4 (BinOp4 ex binOp ey) =
  check_result4
    (eval4 ex)
    ( \vx ->
        check_result4
          (eval4 ey)
          (\vy -> applyBinOp4 vx binOp vy)
          (\t -> BinOp4 (Lit4 vx) binOp t)
    )
    (\t -> BinOp4 t binOp ey)

concatListVs4 :: Value4 -> Value4 -> Maybe Value4
concatListVs4 NilV4 NilV4 = Just NilV4
concatListVs4 NilV4 vs' = Just vs'
concatListVs4 vs NilV4 = Just vs
concatListVs4 (ConsV4 v vs) vs' = ConsV4 v <$> (concatListVs4 vs vs')
concatListVs4 _ _ = Nothing

applyBinOp4 :: Value4 -> BinOpOperator4 -> Value4 -> Result4
applyBinOp4 (IntV4 x) Add4 (IntV4 y) = NoOp4 $ IntV4 (x + y)
applyBinOp4 (IntV4 x) Mul4 (IntV4 y) = NoOp4 $ IntV4 (x * y)
applyBinOp4 vx Concat4 vy = case concatListVs4 vx vy of
  Just v -> NoOp4 v
  Nothing -> error ("Wrong argument types for binary operation: " <> show Concat4)
applyBinOp4 _ binOp _ = error ("Wrong argument types for binary operation: " <> show binOp)

applyUnOp4 :: UnOpOperator4 -> Value4 -> Result4
applyUnOp4 Fst4 (PairV4 x _) = NoOp4 x
applyUnOp4 Snd4 (PairV4 _ x) = NoOp4 x
applyUnOp4 unOp _ = error ("Wrong argument types for unary operation: " <> show unOp)

-- Running is now completely unsafe, so we remove it in favour of safe execution with eval

exp4 :: Expr4
exp4 =
  SHandle4
    ( SHandler4
        "Eff1"
        ( \op v0 resume hdl -> case op of
            "Op1" -> hdl (suspend4 $ resume v0)
        )
        (\v0 -> Lit4 v0)
    )
    (Lit4 $ suspend4 $ BinOp4 (OpCall4 "Eff1" "Op1" (Lit4 (IntV4 86))) Add4 (OpCall4 "Eff1" "Op1" (Lit4 (IntV4 (-102)))))

---------------------------------------------------------------
---- 5 - Unembed name binding
---------------------------------------------------------------
data Value5
  = LambdaV5 String Expr5
  | IntV5 Int
  | BoolV5 Bool
  | PairV5 Value5 Value5
  | UnitV5
  | NilV5
  | ConsV5 Value5 Value5
  | SuspendedV5 (Suspended Expr5)

suspend5 :: Expr5 -> Value5
suspend5 = SuspendedV5 . suspend

data UnOpOperator5 = Fst5 | Snd5 deriving (Show, Eq)

data BinOpOperator5 = Add5 | Mul5 | Concat5 deriving (Show, Eq)

data Expr5
  = Var5 String
  | Lit5 Value5
  | Closed5 Value5
  | OpCall5 String String Expr5
  | Let5 String Expr5 Expr5
  | SHandle5 SHandler5 Expr5
  | If5 Expr5 Expr5 Expr5
  | App5 Expr5 Expr5
  | Pair5 Expr5 Expr5
  | Nil5
  | Cons5 Expr5 Expr5
  | UnOp5 UnOpOperator5 Expr5
  | BinOp5 Expr5 BinOpOperator5 Expr5

-- We only use a name for the parameter, continuation and sub-handler get a keyword:
-- 'resume' for continuations and 'hdl' for recursive handling
data OpI5 = OpI5 String String Expr5

data RetI5 = RetI5 String Expr5

data SHandler5 where
  SHandler5 ::
    String ->
    [OpI5] ->
    RetI5 ->
    SHandler5

data Result5 where
  NoOp5 :: Value5 -> Result5
  Op5 :: String -> String -> Value5 -> (Expr5 -> Expr5) -> Result5

substValue5 :: String -> Value5 -> Value5 -> Value5
substValue5 x v (LambdaV5 y body)
  | x /= y = LambdaV5 y (subst5 x v body)
  | otherwise = LambdaV5 y body
substValue5 x v (PairV5 v1 v2) = PairV5 (substValue5 x v v1) (substValue5 x v v2)
substValue5 x v (ConsV5 v1 v2) = ConsV5 (substValue5 x v v1) (substValue5 x v v2)
substValue5 x v (SuspendedV5 (Suspended e)) = SuspendedV5 (Suspended (subst5 x v e))
substValue5 _ _ v = v

subst5 :: String -> Value5 -> Expr5 -> Expr5
subst5 x v (Var5 y)
  | x == y = Closed5 v
  | otherwise = Var5 y
subst5 x v (Lit5 v') = Lit5 (substValue5 x v v')
subst5 x v (OpCall5 eff op e) = OpCall5 eff op (subst5 x v e)
subst5 x v (Let5 y arg body)
  | x /= y = Let5 y (subst5 x v arg) (subst5 x v body)
  | otherwise = Let5 y (subst5 x v arg) body
subst5 x v (SHandle5 (SHandler5 eff opIs (RetI5 retArgNm retBody)) body) =
  SHandle5
    ( SHandler5
        eff
        ( ( \(OpI5 opNm argNm opBody) ->
              if x /= argNm && x /= "hdl" && x /= "resume"
                then OpI5 opNm argNm (subst5 x v opBody)
                else OpI5 opNm argNm opBody
          )
            <$> opIs
        )
        ( if x /= retArgNm && x /= "hdl" && x /= "resume"
            then RetI5 retArgNm (subst5 x v retBody)
            else RetI5 retArgNm retBody
        )
    )
    (subst5 x v body)
subst5 x v (If5 ce te ee) = If5 (subst5 x v ce) (subst5 x v te) (subst5 x v ee)
subst5 x v (App5 ef ea) = App5 (subst5 x v ef) (subst5 x v ea)
subst5 x v (Pair5 e1 e2) = Pair5 (subst5 x v e1) (subst5 x v e2)
subst5 x v (Cons5 e1 e2) = Cons5 (subst5 x v e1) (subst5 x v e2)
subst5 x v (UnOp5 unOp e1) = UnOp5 unOp (subst5 x v e1)
subst5 x v (BinOp5 e1 binOp e2) = BinOp5 (subst5 x v e1) binOp (subst5 x v e2)
subst5 _ _ e = e

substAll5 :: [(String, Value5)] -> Expr5 -> Expr5
substAll5 [] = id
substAll5 ((x, v) : repls) = subst5 x v . substAll5 repls

check_result5 ::
  Result5 ->
  (Value5 -> Result5) ->
  (Expr5 -> Expr5) ->
  Result5
check_result5 (NoOp5 v) k _ = k v
check_result5 (Op5 eff op va x_op) _ x_op' = Op5 eff op va (x_op' . x_op)

eval5 :: Expr5 -> Result5
eval5 (Var5 nm) = error ("Free variable: " <> nm)
eval5 (Closed5 v) = NoOp5 v
eval5 (Lit5 v) = NoOp5 v
eval5 (OpCall5 eff op ea) =
  check_result5
    (eval5 ea)
    (\v -> Op5 eff op v id)
    (\t -> OpCall5 eff op t)
eval5 (Let5 nm ev body) =
  check_result5
    (eval5 ev)
    (\v -> eval5 (subst5 nm v body))
    (\t -> Let5 nm t body)
eval5 (SHandle5 hlr@(SHandler5 eff ops (RetI5 retArgNm retBody)) seb) =
  case eval5 seb of
    NoOp5 (SuspendedV5 eb) ->
      case eval5 (unSuspend eb) of
        NoOp5 v -> eval5 (subst5 retArgNm v retBody)
        Op5 eff' op va x_op ->
          if eff == eff'
            then
              let OpI5 _ param opI = fromJust $ find (\(OpI5 op' _ _) -> op == op') ops
               in eval5 $
                    substAll5
                      [ (param, va),
                        ("resume", LambdaV5 "___y" (x_op (Var5 "___y"))),
                        ("hdl", LambdaV5 "___y" (SHandle5 hlr (Var5 "___y")))
                      ]
                      opI
            else Op5 eff' op va (SHandle5 hlr . Lit5 . suspend5 . x_op)
    Op5 eff' op va k -> Op5 eff' op va (SHandle5 hlr . k)
--
eval5 (If5 ec ei ee) =
  check_result5
    (eval5 ec)
    ( \(BoolV5 c) ->
        if c
          then eval5 ei
          else eval5 ee
    )
    (\t -> If5 t ei ee)
eval5 (App5 ef ea) =
  check_result5
    (eval5 ef)
    ( \vf@(LambdaV5 param f) ->
        check_result5
          (eval5 ea)
          (\va -> eval5 (subst5 param va f))
          (\t -> App5 (Lit5 vf) t)
    )
    (\t -> App5 t ea)
eval5 (Pair5 e1 e2) =
  check_result5
    (eval5 e1)
    ( \v1 ->
        check_result5
          (eval5 e2)
          (\v2 -> NoOp5 (PairV5 v1 v2))
          (\t -> Pair5 (Lit5 v1) t)
    )
    (\t -> Pair5 t e2)
eval5 Nil5 = NoOp5 NilV5
eval5 (Cons5 e1 e2) =
  check_result5
    (eval5 e1)
    ( \v1 ->
        check_result5
          (eval5 e2)
          (\v2 -> NoOp5 (ConsV5 v1 v2))
          (\t -> Cons5 (Lit5 v1) t)
    )
    (\t -> Cons5 t e2)
eval5 (UnOp5 unOp ex) =
  check_result5
    (eval5 ex)
    (\vx -> applyUnOp5 unOp vx)
    (\t -> UnOp5 unOp t)
eval5 (BinOp5 ex binOp ey) =
  check_result5
    (eval5 ex)
    ( \vx ->
        check_result5
          (eval5 ey)
          (\vy -> applyBinOp5 vx binOp vy)
          (\t -> BinOp5 (Lit5 vx) binOp t)
    )
    (\t -> BinOp5 t binOp ey)

concatListVs5 :: Value5 -> Value5 -> Maybe Value5
concatListVs5 NilV5 NilV5 = Just NilV5
concatListVs5 NilV5 vs' = Just vs'
concatListVs5 vs NilV5 = Just vs
concatListVs5 (ConsV5 v vs) vs' = ConsV5 v <$> (concatListVs5 vs vs')
concatListVs5 _ _ = Nothing

applyBinOp5 :: Value5 -> BinOpOperator5 -> Value5 -> Result5
applyBinOp5 (IntV5 x) Add5 (IntV5 y) = NoOp5 $ IntV5 (x + y)
applyBinOp5 (IntV5 x) Mul5 (IntV5 y) = NoOp5 $ IntV5 (x * y)
applyBinOp5 vx Concat5 vy = case concatListVs5 vx vy of
  Just v -> NoOp5 v
  Nothing -> error ("Wrong argument types for binary operation: " <> show Concat5)
applyBinOp5 _ binOp _ = error ("Wrong argument types for binary operation: " <> show binOp)

applyUnOp5 :: UnOpOperator5 -> Value5 -> Result5
applyUnOp5 Fst5 (PairV5 x _) = NoOp5 x
applyUnOp5 Snd5 (PairV5 _ x) = NoOp5 x
applyUnOp5 unOp _ = error ("Wrong argument types for unary operation: " <> show unOp)

-- exp5 :: Expr5
-- exp5 =
--  SHandle5
--    ( SHandler5
--        [OpI5 "Local5Eff1Op1" "v0" (Hdl5 (App5 (Var5 "resume") (Var5 "v0")))]
--        (RetI5 "v0" (Var5 "v0"))
--    )
--    (BinOp5 (OpCall5 "Local5Eff1Op1" (Lit5 (IntV5 86))) Add5 (OpCall5 "Local5Eff1Op1" (Lit5 (IntV5 (-102)))))

---------------------------------------------------------------
---- Step 6.1. Turn direct-style into CPS
---------------------------------------------------------------
data Value6
  = LambdaV6 String Expr6
  | IntV6 Int
  | BoolV6 Bool
  | PairV6 Value6 Value6
  | UnitV6
  | NilV6
  | ConsV6 Value6 Value6
  | SuspendedV6 (Suspended Expr6)
  deriving (Show, Eq)

suspend6 :: Expr6 -> Value6
suspend6 = SuspendedV6 . suspend

data UnOpOperator6 = Fst6 | Snd6 deriving (Show, Eq)

data BinOpOperator6 = Add6 | Mul6 | Concat6 deriving (Show, Eq)

data Expr6
  = Var6 String
  | Lit6 Value6
  | Closed6 Value6
  | OpCall6 String String Expr6
  | Let6 String Expr6 Expr6
  | SHandle6 SHandler6 Expr6
  | If6 Expr6 Expr6 Expr6
  | App6 Expr6 Expr6
  | Pair6 Expr6 Expr6
  | Nil6
  | Cons6 Expr6 Expr6
  | UnOp6 UnOpOperator6 Expr6
  | BinOp6 Expr6 BinOpOperator6 Expr6
  deriving (Eq, Show)

-- We only use a name for the parameter, continuation and sub-handler get a keyword:
-- 'resume' for continuations and 'hdl' for recursive handling
data OpI6 = OpI6 String String Expr6
  deriving (Eq, Show)

data RetI6 = RetI6 String Expr6
  deriving (Eq, Show)

data SHandler6 = SHandler6 String [OpI6] RetI6
  deriving (Eq, Show)

data ValueOrOp6
  = NoOp6 Value6
  | Op6 String String Value6 (Expr6 -> Expr6)

instance Show ValueOrOp6 where
  show (NoOp6 v) = "NoOp6 " <> show v
  show (Op6 eff op v _) = "Op6 " <> show eff <> " " <> show op <> " " <> show v <> " <func>"

substValue6 :: String -> Value6 -> Value6 -> Value6
substValue6 x v (LambdaV6 y body)
  | x /= y = LambdaV6 y (subst6 x v body)
  | otherwise = LambdaV6 y body
substValue6 x v (PairV6 v1 v2) = PairV6 (substValue6 x v v1) (substValue6 x v v2)
substValue6 x v (ConsV6 v1 v2) = ConsV6 (substValue6 x v v1) (substValue6 x v v2)
substValue6 x v (SuspendedV6 e) = SuspendedV6 (Suspended (subst6 x v (unSuspend e)))
substValue6 _ _ v = v

subst6 :: String -> Value6 -> Expr6 -> Expr6
subst6 x v (Var6 y)
  | x == y = Closed6 v
  | otherwise = Var6 y
subst6 x v (Lit6 v') = Lit6 (substValue6 x v v')
subst6 _ _ (Closed6 v') = Closed6 v'
subst6 x v (OpCall6 eff op e) = OpCall6 eff op (subst6 x v e)
subst6 x v (Let6 y arg body)
  | x /= y = Let6 y (subst6 x v arg) (subst6 x v body)
  | otherwise = Let6 y (subst6 x v arg) body
subst6 x v (SHandle6 (SHandler6 eff opIs (RetI6 retArgNm retBody)) body) =
  SHandle6
    ( SHandler6
        eff
        ( ( \(OpI6 opNm argNm opBody) ->
              if x /= argNm && x /= "hdl" && x /= "resume"
                then OpI6 opNm argNm (subst6 x v opBody)
                else OpI6 opNm argNm opBody
          )
            <$> opIs
        )
        ( if x /= retArgNm && x /= "hdl" && x /= "resume"
            then RetI6 retArgNm (subst6 x v retBody)
            else RetI6 retArgNm retBody
        )
    )
    (subst6 x v body)
subst6 x v (If6 ce te ee) = If6 (subst6 x v ce) (subst6 x v te) (subst6 x v ee)
subst6 x v (App6 ef ea) = App6 (subst6 x v ef) (subst6 x v ea)
subst6 x v (Pair6 e1 e2) = Pair6 (subst6 x v e1) (subst6 x v e2)
subst6 _ _ Nil6 = Nil6
subst6 x v (Cons6 e1 e2) = Cons6 (subst6 x v e1) (subst6 x v e2)
subst6 x v (UnOp6 unOp e1) = UnOp6 unOp (subst6 x v e1)
subst6 x v (BinOp6 e1 binOp e2) = BinOp6 (subst6 x v e1) binOp (subst6 x v e2)

substAll6 :: [(String, Value6)] -> Expr6 -> Expr6
substAll6 [] = id
substAll6 ((x, v) : repls) = subst6 x v . substAll6 repls

substHandleBody6 :: String -> Value6 -> (Expr6 -> Expr6) -> SHandler6 -> Expr6 -> Expr6
substHandleBody6 param va x_op hlr =
  substAll6
    [ (param, va),
      ("hdl", LambdaV6 "___y" (SHandle6 hlr (Var6 "___y"))),
      ("resume", LambdaV6 "___y" (x_op (Var6 "___y")))
    ]

eval6_1 :: Expr6 -> (ValueOrOp6 -> a) -> a
eval6_1 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_1 (Closed6 v) k = k (NoOp6 v)
eval6_1 (Lit6 v) k = k (NoOp6 v)
eval6_1 (OpCall6 eff op ea) k =
  let k1 = \case
        NoOp6 v -> k (Op6 eff op v id)
        Op6 eff' op' va x_op -> k (Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
   in eval6_1 ea k1
eval6_1 (Let6 nm ev body) k =
  let k1 = \case
        NoOp6 v -> eval6_1 (subst6 nm v body) k
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> Let6 nm t body) . x_op))
   in eval6_1 ev k1
eval6_1 (SHandle6 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) seb) k =
  let k1 = \case
        NoOp6 (SuspendedV6 eb) ->
          let k2 = \case
                NoOp6 v -> eval6_1 (subst6 retArgNm v retBody) k
                Op6 eff' op va x_op ->
                  if eff == eff'
                    then
                      let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
                       in eval6_1 (substHandleBody6 param va x_op hlr opI) k
                    else k $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
           in eval6_1 (unSuspend eb) k2
        Op6 eff' op va x_op -> k $ Op6 eff' op va (SHandle6 hlr . x_op)
   in eval6_1 seb k1
--
eval6_1 (If6 ec ei ee) k =
  let k1 = \case
        NoOp6 (BoolV6 c) ->
          if c
            then eval6_1 ei k
            else eval6_1 ee k
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> If6 t ei ee) . x_op))
   in eval6_1 ec k1
eval6_1 (App6 ef ea) k =
  let k1 = \case
        NoOp6 vf@(LambdaV6 param f) ->
          let k2 = \case
                NoOp6 va -> eval6_1 (subst6 param va f) k
                Op6 eff op va x_op -> k (Op6 eff op va ((\t -> App6 (Lit6 vf) t) . x_op))
           in eval6_1 ea k2
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> App6 t ea) . x_op))
   in eval6_1 ef k1
eval6_1 (Pair6 e1 e2) k =
  let k1 = \case
        NoOp6 v1 ->
          let k2 = \case
                NoOp6 v2 -> k (NoOp6 (PairV6 v1 v2))
                Op6 eff op va x_op -> k (Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
           in eval6_1 e2 k2
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> Pair6 t e2) . x_op))
   in eval6_1 e1 k1
eval6_1 Nil6 k = k (NoOp6 NilV6)
eval6_1 (Cons6 e1 e2) k =
  let k1 = \case
        NoOp6 v1 ->
          let k2 = \case
                NoOp6 v2 -> k (NoOp6 (ConsV6 v1 v2))
                Op6 eff op va x_op -> k (Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
           in eval6_1 e2 k2
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> Cons6 t e2) . x_op))
   in eval6_1 e1 k1
eval6_1 (UnOp6 unOp ex) k =
  let k1 = \case
        NoOp6 vx -> k (NoOp6 $ applyUnOp6 unOp vx)
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
   in eval6_1 ex k1
eval6_1 (BinOp6 ex binOp ey) k =
  let k1 = \case
        NoOp6 vx ->
          let k2 = \case
                NoOp6 vy -> k (NoOp6 $ applyBinOp6 vx binOp vy)
                Op6 eff op va x_op -> k (Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
           in eval6_1 ey k2
        Op6 eff op va x_op -> k (Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
   in eval6_1 ex k1

normalise6_1 :: Expr6 -> ValueOrOp6
normalise6_1 e = eval6_1 e id

concatListVs6 :: Value6 -> Value6 -> Maybe Value6
concatListVs6 NilV6 NilV6 = Just NilV6
concatListVs6 NilV6 vs' = Just vs'
concatListVs6 vs NilV6 = Just vs
concatListVs6 (ConsV6 v vs) vs' = ConsV6 v <$> concatListVs6 vs vs'
concatListVs6 _ _ = Nothing

applyBinOp6 :: Value6 -> BinOpOperator6 -> Value6 -> Value6
applyBinOp6 (IntV6 x) Add6 (IntV6 y) = IntV6 (x + y)
applyBinOp6 (IntV6 x) Mul6 (IntV6 y) = IntV6 (x * y)
applyBinOp6 vx Concat6 vy = case concatListVs6 vx vy of
  Just v -> v
  Nothing -> error ("Wrong argument types for binary operation: " <> show Concat6)
applyBinOp6 _ binOp _ = error ("Wrong argument types for binary operation: " <> show binOp)

applyUnOp6 :: UnOpOperator6 -> Value6 -> Value6
applyUnOp6 Fst6 (PairV6 x _) = x
applyUnOp6 Snd6 (PairV6 _ x) = x
applyUnOp6 unOp _ = error ("Wrong argument types for unary operation: " <> show unOp)

---------------------------------------------------------------
---- Step 6.2. Adding congruence cases where necessary
---------------------------------------------------------------
type K2 = ValueOrOp6 :+: Expr6

eval6_2 :: Expr6 -> (K2 -> a) -> a
eval6_2 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_2 (Closed6 v) k = k (inj0 $ NoOp6 v)
eval6_2 (Lit6 v) k = k (inj0 $ NoOp6 v)
eval6_2 (OpCall6 eff op ea) k =
  let k1 = \case
        Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
        Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
        Inr0 ea' -> eval6_2 ea' k1
   in eval6_2 ea k1
eval6_2 (Let6 nm ev body) k =
  let k1 = \case
        Inl0 (NoOp6 v) -> eval6_2 (subst6 nm v body) k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
        Inr0 ev' -> eval6_2 ev' k1
   in eval6_2 ev k1
eval6_2 (SHandle6 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) seb) k =
  let k1 = \case
        Inl0 (NoOp6 (SuspendedV6 eb)) ->
          let k2 = \case
                Inl0 (NoOp6 v) -> eval6_2 (subst6 retArgNm v retBody) k
                Inl0 (Op6 eff' op va x_op) ->
                  if eff == eff'
                    then
                      let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
                       in eval6_2 (substHandleBody6 param va x_op hlr opI) k
                    else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
                Inr0 eb' -> eval6_2 eb' k2
           in eval6_2 (unSuspend eb) k2
        Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
        Inr0 seb' -> eval6_2 seb' k1
   in eval6_2 seb k1
--
eval6_2 (If6 ec ei ee) k =
  let k1 = \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_2 ei k
            else eval6_2 ee k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
        Inr0 ec' -> eval6_2 ec' k1
   in eval6_2 ec k1
eval6_2 (App6 ef ea) k =
  let k1 = \case
        Inl0 (NoOp6 vf@(LambdaV6 param f)) ->
          let k2 = \case
                Inl0 (NoOp6 va) -> eval6_2 (subst6 param va f) k
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 vf) t) . x_op))
                Inr0 ea' -> eval6_2 ea' k2
           in eval6_2 ea k2
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
        Inr0 ef' -> eval6_2 ef' k1
   in eval6_2 ef k1
eval6_2 (Pair6 e1 e2) k =
  let k1 = \case
        Inl0 (NoOp6 v1) ->
          let k2 = \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> eval6_2 e2' k2
           in eval6_2 e2 k2
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
        Inr0 e1' -> eval6_2 e1' k1
   in eval6_2 e1 k1
eval6_2 Nil6 k = k (inj0 $ NoOp6 NilV6)
eval6_2 (Cons6 e1 e2) k =
  let k1 = \case
        Inl0 (NoOp6 v1) ->
          let k2 = \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> eval6_2 e2' k2
           in eval6_2 e2 k2
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
        Inr0 e1' -> eval6_2 e1' k1
   in eval6_2 e1 k1
eval6_2 (UnOp6 unOp ex) k =
  let k1 = \case
        Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
        Inr0 ex' -> eval6_2 ex' k1
   in eval6_2 ex k1
eval6_2 (BinOp6 ex binOp ey) k =
  let k1 = \case
        Inl0 (NoOp6 vx) ->
          let k2 = \case
                Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
                Inr0 ey' -> eval6_2 ey' k2
           in eval6_2 ey k2
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
        Inr0 ex' -> eval6_2 ex' k1
   in eval6_2 ex k1

normalise6_2 :: Expr6 -> ValueOrOp6
normalise6_2 e = eval6_2 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_2 e' k

---------------------------------------------------------------
---- Step 6.3. Argument lifting
---------------------------------------------------------------
type K3 = ValueOrOp6 :+: Expr6

eval6_3 :: Expr6 -> (K3 -> ValueOrOp6) -> ValueOrOp6
eval6_3 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_3 (Closed6 v) k = k (inj0 $ NoOp6 v)
eval6_3 (Lit6 v) k = k (inj0 $ NoOp6 v)
eval6_3 (OpCall6 eff op ea) k =
  let k1 eff op = \case
        Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
        Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
        Inr0 ea' -> eval6_3 ea' (k1 eff op)
   in eval6_3 ea (k1 eff op)
eval6_3 (Let6 nm ev body) k =
  let k1 nm body = \case
        Inl0 (NoOp6 v) -> eval6_3 (subst6 nm v body) k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
        Inr0 ev' -> eval6_3 ev' (k1 nm body)
   in eval6_3 ev (k1 nm body)
eval6_3 (SHandle6 hlr seb) k =
  let k1 hlr = \case
        Inl0 (NoOp6 (SuspendedV6 eb)) ->
          let k2 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) = \case
                Inl0 (NoOp6 v) -> eval6_3 (subst6 retArgNm v retBody) k
                Inl0 (Op6 eff' op va x_op) ->
                  if eff == eff'
                    then
                      let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
                       in eval6_3 (substHandleBody6 param va x_op hlr opI) k
                    else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
                Inr0 eb' -> eval6_3 eb' (k2 hlr)
           in eval6_3 (unSuspend eb) (k2 hlr)
        Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
        Inr0 seb' -> eval6_3 seb' (k1 hlr)
   in eval6_3 seb (k1 hlr)
--
eval6_3 (If6 ec ei ee) k =
  let k1 ei ee = \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_3 ei k
            else eval6_3 ee k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
        Inr0 ec' -> eval6_3 ec' (k1 ei ee)
   in eval6_3 ec (k1 ei ee)
eval6_3 (App6 ef ea) k =
  let k1 ea = \case
        Inl0 (NoOp6 (LambdaV6 param f)) ->
          let k2 param body = \case
                Inl0 (NoOp6 va) -> eval6_3 (subst6 param va f) k
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op))
                Inr0 ea' -> eval6_3 ea' (k2 param f)
           in eval6_3 ea (k2 param f)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
        Inr0 ef' -> eval6_3 ef' (k1 ea)
   in eval6_3 ef (k1 ea)
eval6_3 (Pair6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> eval6_3 e2' (k2 v1)
           in eval6_3 e2 (k2 v1)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
        Inr0 e1' -> eval6_3 e1' (k1 e2)
   in eval6_3 e1 (k1 e2)
eval6_3 Nil6 k = k (inj0 $ NoOp6 NilV6)
eval6_3 (Cons6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> eval6_3 e2' (k2 v1)
           in eval6_3 e2 (k2 v1)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
        Inr0 e1' -> eval6_3 e1' (k1 e2)
   in eval6_3 e1 (k1 e2)
eval6_3 (UnOp6 unOp ex) k =
  let k1 unOp = \case
        Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
        Inr0 ex' -> eval6_3 ex' (k1 unOp)
   in eval6_3 ex (k1 unOp)
eval6_3 (BinOp6 ex binOp ey) k =
  let k1 binOp ey = \case
        Inl0 (NoOp6 vx) ->
          let k2 vx binOp = \case
                Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
                Inr0 ey' -> eval6_3 ey' (k2 vx binOp)
           in eval6_3 ey (k2 vx binOp)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
        Inr0 ex' -> eval6_3 ex' (k1 binOp ey)
   in eval6_3 ex (k1 binOp ey)

normalise6_3 :: Expr6 -> ValueOrOp6
normalise6_3 e = eval6_3 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_3 e' k

---------------------------------------------------------------
---- Step 6.4. Continuations switch control
---------------------------------------------------------------
type K4 = ValueOrOp6 :+: Expr6

eval6_4 :: Expr6 -> (K4 -> ValueOrOp6) -> ValueOrOp6
eval6_4 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_4 (Closed6 v) k = k (inj0 $ NoOp6 v)
eval6_4 (Lit6 v) k = k (inj0 $ NoOp6 v)
eval6_4 (OpCall6 eff op ea) k =
  let k1 eff op = \case
        Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
        Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
        Inr0 ea' -> eval6_4 ea' (k1 eff op)
   in k1 eff op (inj0 ea)
eval6_4 (Let6 nm ev body) k =
  let k1 nm body = \case
        Inl0 (NoOp6 v) -> eval6_4 (subst6 nm v body) k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
        Inr0 ev' -> eval6_4 ev' (k1 nm body)
   in k1 nm body (inj0 ev)
eval6_4 (SHandle6 hlr seb) k =
  let k1 hlr = \case
        Inl0 (NoOp6 (SuspendedV6 eb)) ->
          let k2 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) = \case
                Inl0 (NoOp6 v) -> eval6_4 (subst6 retArgNm v retBody) k
                Inl0 (Op6 eff' op va x_op) ->
                  if eff == eff'
                    then
                      let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
                       in eval6_4 (substHandleBody6 param va x_op hlr opI) k
                    else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
                Inr0 eb' -> eval6_4 eb' (k2 hlr)
           in k2 hlr (inj0 $ unSuspend eb)
        Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
        Inr0 seb' -> eval6_4 seb' (k1 hlr)
   in k1 hlr (inj0 seb)
--
eval6_4 (If6 ec ei ee) k =
  let k1 ei ee = \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_4 ei k
            else eval6_4 ee k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
        Inr0 ec' -> eval6_4 ec' (k1 ei ee)
   in k1 ei ee (inj0 ec)
eval6_4 (App6 ef ea) k =
  let k1 ea = \case
        Inl0 (NoOp6 (LambdaV6 param body)) ->
          let k2 param body = \case
                Inl0 (NoOp6 va) -> eval6_4 (subst6 param va body) k
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op))
                Inr0 ea' -> eval6_4 ea' (k2 param body)
           in k2 param body (inj0 ea)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
        Inr0 ef' -> eval6_4 ef' (k1 ea)
   in k1 ea (inj0 ef)
eval6_4 (Pair6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> eval6_4 e2' (k2 v1)
           in k2 v1 (inj0 e2)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
        Inr0 e1' -> eval6_4 e1' (k1 e2)
   in k1 e2 (inj0 e1)
eval6_4 Nil6 k = k (inj0 $ NoOp6 NilV6)
eval6_4 (Cons6 e1 e2) k =
  let k1 e2 = \case
        Inl0 (NoOp6 v1) ->
          let k2 v1 = \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> eval6_4 e2' (k2 v1)
           in k2 v1 (inj0 e2)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
        Inr0 e1' -> eval6_4 e1' (k1 e2)
   in k1 e2 (inj0 e1)
eval6_4 (UnOp6 unOp ex) k =
  let k1 unOp = \case
        Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
        Inr0 ex' -> eval6_4 ex' (k1 unOp)
   in k1 unOp (inj0 ex)
eval6_4 (BinOp6 ex binOp ey) k =
  let k1 binOp ey = \case
        Inl0 (NoOp6 vx) ->
          let k2 vx binOp = \case
                Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
                Inr0 ey' -> eval6_4 ey' (k2 vx binOp)
           in k2 vx binOp (inj0 ey)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
        Inr0 ex' -> eval6_4 ex' (k1 binOp ey)
   in k1 binOp ey (inj0 ex)

normalise6_4 :: Expr6 -> ValueOrOp6
normalise6_4 e = eval6_4 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_4 e' k

---------------------------------------------------------------
---- Step 6.5. Defunctionalisation
---------------------------------------------------------------
data Continuation5
  = Cont5OpCall String String K5
  | Cont5Let String Expr6 K5
  | Cont5Handle1 SHandler6 K5
  | Cont5Handle2 SHandler6 K5
  | Cont5If Expr6 Expr6 K5
  | Cont5App1 Expr6 K5
  | Cont5App2 String Expr6 K5
  | Cont5Pair1 Expr6 K5
  | Cont5Pair2 Value6 K5
  | Cont5Cons1 Expr6 K5
  | Cont5Cons2 Value6 K5
  | Cont5UnOp UnOpOperator6 K5
  | Cont5BinOp1 BinOpOperator6 Expr6 K5
  | Cont5BinOp2 Value6 BinOpOperator6 K5

type K5 = ValueOrOp6 :+: Expr6

apply6_5 :: Continuation5 -> (K5 -> ValueOrOp6) -> ValueOrOp6
apply6_5 (Cont5OpCall eff op ea) k = case ea of
  Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
  Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
  Inr0 ea' -> eval6_5 ea' (\ea'' -> apply6_5 (Cont5OpCall eff op ea'') k)
apply6_5 (Cont5Let nm body ev) k = case ev of
  Inl0 (NoOp6 v) -> eval6_5 (subst6 nm v body) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
  Inr0 ev' -> eval6_5 ev' (\ev'' -> apply6_5 (Cont5Let nm body ev'') k)
apply6_5 (Cont5Handle1 hlr seb) k = case seb of
  Inl0 (NoOp6 (SuspendedV6 eb)) -> apply6_5 (Cont5Handle2 hlr (inj0 $ unSuspend eb)) k
  Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
  Inr0 seb' -> eval6_5 seb' (\seb'' -> apply6_5 (Cont5Handle1 hlr seb'') k)
apply6_5 (Cont5Handle2 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) eb) k = case eb of
  Inl0 (NoOp6 v) -> eval6_5 (subst6 retArgNm v retBody) k
  Inl0 (Op6 eff' op va x_op) ->
    if eff == eff'
      then
        let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
         in eval6_5 (substHandleBody6 param va x_op hlr opI) k
      else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
  Inr0 eb' -> eval6_5 eb' (\eb'' -> apply6_5 (Cont5Handle2 hlr eb'') k)
--
apply6_5 (Cont5If ei ee ec) k = case ec of
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_5 ei k
      else eval6_5 ee k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
  Inr0 ec' -> eval6_5 ec' (\ec'' -> apply6_5 (Cont5If ei ee ec'') k)
apply6_5 (Cont5App1 ea ef) k = case ef of
  Inl0 (NoOp6 (LambdaV6 param body)) -> apply6_5 (Cont5App2 param body (inj0 ea)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
  Inr0 ef' -> eval6_5 ef' (\ef'' -> apply6_5 (Cont5App1 ea ef'') k)
apply6_5 (Cont5App2 param body ea) k = case ea of
  Inl0 (NoOp6 va) -> eval6_5 (subst6 param va body) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op))
  Inr0 ea' -> eval6_5 ea' (\ea'' -> apply6_5 (Cont5App2 param body ea'') k)
apply6_5 (Cont5Pair1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_5 (Cont5Pair2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
  Inr0 e1' -> eval6_5 e1' (\e1'' -> apply6_5 (Cont5Pair1 e2 e1'') k)
apply6_5 (Cont5Pair2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
  Inr0 e2' -> eval6_5 e2' (\e2'' -> apply6_5 (Cont5Pair2 v1 e2'') k)
apply6_5 (Cont5Cons1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_5 (Cont5Cons2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
  Inr0 e1' -> eval6_5 e1' (\e1'' -> apply6_5 (Cont5Cons1 e2 e1'') k)
apply6_5 (Cont5Cons2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
  Inr0 e2' -> eval6_5 e2' (\e2'' -> apply6_5 (Cont5Cons2 v1 e2'') k)
apply6_5 (Cont5UnOp unOp ex) k = case ex of
  Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
  Inr0 ex' -> eval6_5 ex' (\ex'' -> apply6_5 (Cont5UnOp unOp ex'') k)
apply6_5 (Cont5BinOp1 binOp ey ex) k = case ex of
  Inl0 (NoOp6 vx) -> apply6_5 (Cont5BinOp2 vx binOp (inj0 ey)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
  Inr0 ex' -> eval6_5 ex' (\ex'' -> apply6_5 (Cont5BinOp1 binOp ey ex'') k)
apply6_5 (Cont5BinOp2 vx binOp ey) k = case ey of
  Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
  Inr0 ey' -> eval6_5 ey' (\ey'' -> apply6_5 (Cont5BinOp2 vx binOp ey'') k)

eval6_5 :: Expr6 -> (K5 -> ValueOrOp6) -> ValueOrOp6
eval6_5 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_5 (Closed6 v) k = k (inj0 $ NoOp6 v)
eval6_5 (Lit6 v) k = k (inj0 $ NoOp6 v)
eval6_5 (OpCall6 eff op ea) k = apply6_5 (Cont5OpCall eff op (inj0 ea)) k
eval6_5 (Let6 nm ev body) k = apply6_5 (Cont5Let nm body (inj0 ev)) k
eval6_5 (SHandle6 hlr eb) k = apply6_5 (Cont5Handle1 hlr (inj0 eb)) k
--
eval6_5 (If6 ec ei ee) k = apply6_5 (Cont5If ei ee (inj0 ec)) k
eval6_5 (App6 ef ea) k = apply6_5 (Cont5App1 ea (inj0 ef)) k
eval6_5 (Pair6 e1 e2) k = apply6_5 (Cont5Pair1 e2 (inj0 e1)) k
eval6_5 Nil6 k = k (inj0 $ NoOp6 NilV6)
eval6_5 (Cons6 e1 e2) k = apply6_5 (Cont5Cons1 e2 (inj0 e1)) k
eval6_5 (UnOp6 unOp ex) k = apply6_5 (Cont5UnOp unOp (inj0 ex)) k
eval6_5 (BinOp6 ex binOp ey) k = apply6_5 (Cont5BinOp1 binOp ey (inj0 ex)) k

normalise6_5 :: Expr6 -> ValueOrOp6
normalise6_5 e = eval6_5 e k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_5 e' k

---------------------------------------------------------------
---- Step 6.6. Remove tail-calls
---------------------------------------------------------------
data Continuation6
  = Cont6OpCall String String K6
  | Cont6Let String Expr6 K6
  | Cont6Handle1 SHandler6 K6
  | Cont6Handle2 SHandler6 K6
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

type K6 = ValueOrOp6 :+: Expr6 :+: Continuation6

apply6_6 :: Continuation6 -> (K6 -> ValueOrOp6) -> ValueOrOp6
apply6_6 (Cont6OpCall eff op ea) k = case ea of
  Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
  Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
  Inr0 ea' -> eval6_6 ea' (\ea'' -> k (inj0 (Cont6OpCall eff op ea'')))
apply6_6 (Cont6Let nm body ev) k = case ev of
  Inl0 (NoOp6 v) -> eval6_6 (inj0 (subst6 nm v body)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
  Inr0 ev' -> eval6_6 ev' (\ev'' -> k (inj0 (Cont6Let nm body ev'')))
apply6_6 (Cont6Handle1 hlr seb) k = case seb of
  Inl0 (NoOp6 (SuspendedV6 eb)) -> apply6_6 (Cont6Handle2 hlr (inj0 $ unSuspend eb)) k
  Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
  Inr0 seb' -> eval6_6 seb' (\seb'' -> k (inj0 $ Cont6Handle1 hlr seb''))
apply6_6 (Cont6Handle2 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) eb) k = case eb of
  Inl0 (NoOp6 v) -> eval6_6 (inj0 $ subst6 retArgNm v retBody) k
  Inl0 (Op6 eff' op va x_op) ->
    if eff == eff'
      then
        let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
         in eval6_6 (inj0 $ substHandleBody6 param va x_op hlr opI) k
      else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
  Inr0 eb' -> eval6_6 eb' (\eb'' -> k (inj0 $ Cont6Handle2 hlr eb''))
--
apply6_6 (Cont6If ei ee ec) k = case ec of
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_6 (inj0 ei) k
      else eval6_6 (inj0 ee) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
  Inr0 ec' -> eval6_6 ec' (\ec'' -> k (inj0 $ Cont6If ei ee ec''))
apply6_6 (Cont6App1 ea ef) k = case ef of
  Inl0 (NoOp6 (LambdaV6 param body)) -> apply6_6 (Cont6App2 param body (inj0 ea)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
  Inr0 ef' -> eval6_6 ef' (\ef'' -> k (inj0 $ Cont6App1 ea ef''))
apply6_6 (Cont6App2 param body ea) k = case ea of
  Inl0 (NoOp6 va) -> eval6_6 (inj0 $ subst6 param va body) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op))
  Inr0 ea' -> eval6_6 ea' (\ea'' -> k (inj0 $ Cont6App2 param body ea''))
apply6_6 (Cont6Pair1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_6 (Cont6Pair2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
  Inr0 e1' -> eval6_6 e1' (\e1'' -> k (inj0 $ Cont6Pair1 e2 e1''))
apply6_6 (Cont6Pair2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
  Inr0 e2' -> eval6_6 e2' (\e2'' -> k (inj0 $ Cont6Pair2 v1 e2''))
apply6_6 (Cont6Cons1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_6 (Cont6Cons2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
  Inr0 e1' -> eval6_6 e1' (\e1'' -> k (inj0 $ Cont6Cons1 e2 e1''))
apply6_6 (Cont6Cons2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
  Inr0 e2' -> eval6_6 e2' (\e2'' -> k (inj0 $ Cont6Cons2 v1 e2''))
apply6_6 (Cont6UnOp unOp ex) k = case ex of
  Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
  Inr0 ex' -> eval6_6 ex' (\ex'' -> k (inj0 $ Cont6UnOp unOp ex''))
apply6_6 (Cont6BinOp1 binOp ey ex) k = case ex of
  Inl0 (NoOp6 vx) -> apply6_6 (Cont6BinOp2 vx binOp (inj0 ey)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
  Inr0 ex' -> eval6_6 ex' (\ex'' -> k (inj0 $ Cont6BinOp1 binOp ey ex''))
apply6_6 (Cont6BinOp2 vx binOp ey) k = case ey of
  Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
  Inr0 ey' -> eval6_6 ey' (\ey'' -> k (inj0 $ Cont6BinOp2 vx binOp ey''))

eval6_6 :: Expr6 :+: Continuation6 -> (K6 -> ValueOrOp6) -> ValueOrOp6
eval6_6 (Inr0 c) k = apply6_6 c k
eval6_6 (Inl0 (Var6 nm)) _ = error ("Free variable: " <> nm)
eval6_6 (Inl0 (Closed6 v)) k = k (inj0 $ NoOp6 v)
eval6_6 (Inl0 (Lit6 v)) k = k (inj0 $ NoOp6 v)
eval6_6 (Inl0 (OpCall6 eff op ea)) k = apply6_6 (Cont6OpCall eff op (inj0 ea)) k
eval6_6 (Inl0 (Let6 nm ev body)) k = apply6_6 (Cont6Let nm body (inj0 ev)) k
eval6_6 (Inl0 (SHandle6 hlr eb)) k = apply6_6 (Cont6Handle1 hlr (inj0 eb)) k
--
eval6_6 (Inl0 (If6 ec ei ee)) k = apply6_6 (Cont6If ei ee (inj0 ec)) k
eval6_6 (Inl0 (App6 ef ea)) k = apply6_6 (Cont6App1 ea (inj0 ef)) k
eval6_6 (Inl0 (Pair6 e1 e2)) k = apply6_6 (Cont6Pair1 e2 (inj0 e1)) k
eval6_6 (Inl0 Nil6) k = k (inj0 $ NoOp6 NilV6)
eval6_6 (Inl0 (Cons6 e1 e2)) k = apply6_6 (Cont6Cons1 e2 (inj0 e1)) k
eval6_6 (Inl0 (UnOp6 unOp ex)) k = apply6_6 (Cont6UnOp unOp (inj0 ex)) k
eval6_6 (Inl0 (BinOp6 ex binOp ey)) k = apply6_6 (Cont6BinOp1 binOp ey (inj0 ex)) k

normalise6_6 :: Expr6 -> ValueOrOp6
normalise6_6 e = eval6_6 (inj0 e) k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_6 e' k

---------------------------------------------------------------
---- Step 6.7. Turn continuations into terms
---------------------------------------------------------------
data Continuation7
  = Cont7OpCall String String K7
  | Cont7Let String Expr6 K7
  | Cont7Handle1 SHandler6 K7
  | Cont7Handle2 SHandler6 K7
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

type K7 = ValueOrOp6 :+: Expr6

apply6_7 :: Continuation7 -> (K7 -> ValueOrOp6) -> ValueOrOp6
apply6_7 (Cont7OpCall eff op ea) k = case ea of
  Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
  Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
  Inr0 ea' ->
    eval6_7
      ea'
      ( \case
          Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
          Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
          Inr0 ea'' -> k (inj0 (OpCall6 eff op ea''))
      )
apply6_7 (Cont7Let nm body ev) k = case ev of
  Inl0 (NoOp6 v) -> eval6_7 (subst6 nm v body) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
  Inr0 ev' ->
    eval6_7
      ev'
      ( \case
          Inl0 (NoOp6 v) -> eval6_7 (subst6 nm v body) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
          Inr0 ev'' -> k (inj0 (Let6 nm ev'' body))
      )
apply6_7 (Cont7Handle1 hlr seb) k = case seb of
  Inl0 (NoOp6 (SuspendedV6 eb)) -> apply6_7 (Cont7Handle2 hlr (inj0 $ unSuspend eb)) k
  Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
  Inr0 seb' -> eval6_7 seb' $ \case
    Inl0 (NoOp6 (SuspendedV6 eb)) -> apply6_7 (Cont7Handle2 hlr (inj0 $ unSuspend eb)) k
    Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
    Inr0 seb'' -> k (inj0 $ SHandle6 hlr seb'')
apply6_7 (Cont7Handle2 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) eb) k = case eb of
  Inl0 (NoOp6 v) -> eval6_7 (inj0 $ subst6 retArgNm v retBody) k
  Inl0 (Op6 eff' op va x_op) ->
    if eff == eff'
      then
        let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
         in eval6_7 (inj0 $ substHandleBody6 param va x_op hlr opI) k
      else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
  Inr0 eb' -> eval6_7 eb' $ \case
    Inl0 (NoOp6 v) -> eval6_7 (inj0 $ subst6 retArgNm v retBody) k
    Inl0 (Op6 eff' op va x_op) ->
      if eff == eff'
        then
          let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
           in eval6_7 (inj0 $ substHandleBody6 param va x_op hlr opI) k
        else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
    Inr0 eb'' -> k (inj0 $ SHandle6 hlr $ Lit6 $ suspend6 eb'')
--
apply6_7 (Cont7If ei ee ec) k = case ec of
  Inl0 (NoOp6 (BoolV6 c)) ->
    if c
      then eval6_7 (inj0 ei) k
      else eval6_7 (inj0 ee) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
  Inr0 ec' ->
    eval6_7
      ec'
      ( \case
          Inl0 (NoOp6 (BoolV6 c)) ->
            if c
              then eval6_7 (inj0 ei) k
              else eval6_7 (inj0 ee) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
          Inr0 ec'' -> k (inj0 $ If6 ec'' ei ee)
      )
apply6_7 (Cont7App1 ea ef) k = case ef of
  Inl0 (NoOp6 (LambdaV6 param body)) -> apply6_7 (Cont7App2 param body (inj0 ea)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
  Inr0 ef' ->
    eval6_7
      ef'
      ( \case
          Inl0 (NoOp6 (LambdaV6 param body)) -> apply6_7 (Cont7App2 param body (inj0 ea)) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
          Inr0 ef'' -> k (inj0 $ App6 ef'' ea)
      )
apply6_7 (Cont7App2 param body ea) k = case ea of
  Inl0 (NoOp6 va) -> eval6_7 (inj0 $ subst6 param va body) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op))
  Inr0 ea' ->
    eval6_7
      ea'
      ( \case
          Inl0 (NoOp6 va) -> eval6_7 (inj0 $ subst6 param va body) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param body)) t) . x_op))
          Inr0 ea'' -> k (inj0 $ App6 (Lit6 (LambdaV6 param body)) ea'')
      )
apply6_7 (Cont7Pair1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_7 (Cont7Pair2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
  Inr0 e1' ->
    eval6_7
      e1'
      ( \case
          Inl0 (NoOp6 v1) -> apply6_7 (Cont7Pair2 v1 (inj0 e2)) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
          Inr0 e1'' -> k (inj0 $ Pair6 e1'' e2)
      )
apply6_7 (Cont7Pair2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
  Inr0 e2' ->
    eval6_7
      e2'
      ( \case
          Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
          Inr0 e2'' -> k (inj0 $ Pair6 (Lit6 v1) e2'')
      )
apply6_7 (Cont7Cons1 e2 e1) k = case e1 of
  Inl0 (NoOp6 v1) -> apply6_7 (Cont7Cons2 v1 (inj0 e2)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
  Inr0 e1' ->
    eval6_7
      e1'
      ( \case
          Inl0 (NoOp6 v1) -> apply6_7 (Cont7Cons2 v1 (inj0 e2)) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
          Inr0 e1'' -> k (inj0 $ Cons6 e1'' e2)
      )
apply6_7 (Cont7Cons2 v1 e2) k = case e2 of
  Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
  Inr0 e2' ->
    eval6_7
      e2'
      ( \case
          Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
          Inr0 e2'' -> k (inj0 $ Cons6 (Lit6 v1) e2'')
      )
apply6_7 (Cont7UnOp unOp ex) k = case ex of
  Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
  Inr0 ex' ->
    eval6_7
      ex'
      ( \case
          Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
          Inr0 ex'' -> k (inj0 $ UnOp6 unOp ex'')
      )
apply6_7 (Cont7BinOp1 binOp ey ex) k = case ex of
  Inl0 (NoOp6 vx) -> apply6_7 (Cont7BinOp2 vx binOp (inj0 ey)) k
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
  Inr0 ex' ->
    eval6_7
      ex'
      ( \case
          Inl0 (NoOp6 vx) -> apply6_7 (Cont7BinOp2 vx binOp (inj0 ey)) k
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
          Inr0 ex'' -> k (inj0 $ BinOp6 ex'' binOp ey)
      )
apply6_7 (Cont7BinOp2 vx binOp ey) k = case ey of
  Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
  Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
  Inr0 ey' ->
    eval6_7
      ey'
      ( \case
          Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
          Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
          Inr0 ey'' -> k (inj0 $ BinOp6 (Lit6 vx) binOp ey'')
      )

eval6_7 :: Expr6 -> (K7 -> ValueOrOp6) -> ValueOrOp6
eval6_7 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_7 (Closed6 v) k = k (inj0 $ NoOp6 v)
eval6_7 (Lit6 v) k = k (inj0 $ NoOp6 v)
eval6_7 (OpCall6 eff op ea) k = apply6_7 (Cont7OpCall eff op (inj0 ea)) k
eval6_7 (Let6 nm ev body) k = apply6_7 (Cont7Let nm body (inj0 ev)) k
eval6_7 (SHandle6 hlr eb) k = apply6_7 (Cont7Handle1 hlr (inj0 eb)) k
--
eval6_7 (If6 ec ei ee) k = apply6_7 (Cont7If ei ee (inj0 ec)) k
eval6_7 (App6 ef ea) k = apply6_7 (Cont7App1 ea (inj0 ef)) k
eval6_7 (Pair6 e1 e2) k = apply6_7 (Cont7Pair1 e2 (inj0 e1)) k
eval6_7 Nil6 k = k (inj0 $ NoOp6 NilV6)
eval6_7 (Cons6 e1 e2) k = apply6_7 (Cont7Cons1 e2 (inj0 e1)) k
eval6_7 (UnOp6 unOp ex) k = apply6_7 (Cont7UnOp unOp (inj0 ex)) k
eval6_7 (BinOp6 ex binOp ey) k = apply6_7 (Cont7BinOp1 binOp ey (inj0 ex)) k

normalise6_7 :: Expr6 -> ValueOrOp6
normalise6_7 e = eval6_7 (inj0 e) k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_7 e' k

---------------------------------------------------------------
---- Step 6.8. Inlining and simplification
---------------------------------------------------------------
type K8 = ValueOrOp6 :+: Expr6

eval6_8 :: Expr6 -> (K8 -> ValueOrOp6) -> ValueOrOp6
eval6_8 (Var6 nm) _ = error ("Free variable: " <> nm)
eval6_8 (Closed6 v) k = k (inj0 $ NoOp6 v)
eval6_8 (Lit6 v) k = k (inj0 $ NoOp6 v)
eval6_8 (OpCall6 eff op ea) k =
  eval6_8
    ea
    ( \case
        Inl0 (NoOp6 v) -> k (inj0 $ Op6 eff op v id)
        Inl0 (Op6 eff' op' va x_op) -> k (inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op))
        Inr0 ea' -> k (inj0 (OpCall6 eff op ea'))
    )
eval6_8 (Let6 nm ev body) k =
  eval6_8
    ev
    ( \case
        Inl0 (NoOp6 v) -> eval6_8 (subst6 nm v body) k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op))
        Inr0 ev' -> k (inj0 (Let6 nm ev' body))
    )
eval6_8 (SHandle6 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) seb) k =
  eval6_8 seb $ \case
    Inl0 (NoOp6 (SuspendedV6 eb)) ->
      eval6_8 (unSuspend eb) $ \case
        Inl0 (NoOp6 v) -> eval6_8 (subst6 retArgNm v retBody) k
        Inl0 (Op6 eff' op va x_op) ->
          if eff == eff'
            then
              let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
               in eval6_8 (substHandleBody6 param va x_op hlr opI) k
            else k $ inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
        Inr0 eb' -> k (inj0 $ SHandle6 hlr $ Lit6 $ suspend6 eb')
    Inl0 (Op6 eff' op va x_op) -> k $ inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
    Inr0 seb' -> k (inj0 $ SHandle6 hlr seb')
--
eval6_8 (If6 ec ei ee) k =
  eval6_8
    ec
    ( \case
        Inl0 (NoOp6 (BoolV6 c)) ->
          if c
            then eval6_8 (inj0 ei) k
            else eval6_8 (inj0 ee) k
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op))
        Inr0 ec' -> k (inj0 $ If6 ec' ei ee)
    )
eval6_8 (App6 ef ea) k =
  eval6_8
    ef
    ( \case
        Inl0 (NoOp6 (LambdaV6 param f)) ->
          eval6_8
            ea
            ( \case
                Inl0 (NoOp6 va) -> eval6_8 (inj0 $ subst6 param va f) k
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op))
                Inr0 ea' -> k (inj0 $ App6 (Lit6 (LambdaV6 param f)) ea')
            )
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op))
        Inr0 ef' -> k (inj0 $ App6 ef' ea)
    )
eval6_8 (Pair6 e1 e2) k =
  eval6_8
    e1
    ( \case
        Inl0 (NoOp6 v1) ->
          eval6_8
            e2
            ( \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (PairV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> k (inj0 $ Pair6 (Lit6 v1) e2')
            )
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op))
        Inr0 e1' -> k (inj0 $ Pair6 e1' e2)
    )
eval6_8 Nil6 k = k (inj0 $ NoOp6 NilV6)
eval6_8 (Cons6 e1 e2) k =
  eval6_8
    e1
    ( \case
        Inl0 (NoOp6 v1) ->
          eval6_8
            e2
            ( \case
                Inl0 (NoOp6 v2) -> k (inj0 $ NoOp6 (ConsV6 v1 v2))
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op))
                Inr0 e2' -> k (inj0 $ Cons6 (Lit6 v1) e2')
            )
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op))
        Inr0 e1' -> k (inj0 $ Cons6 e1' e2)
    )
eval6_8 (UnOp6 unOp ex) k =
  eval6_8
    ex
    ( \case
        Inl0 (NoOp6 vx) -> k (inj0 $ NoOp6 $ applyUnOp6 unOp vx)
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op))
        Inr0 ex' -> k (inj0 $ UnOp6 unOp ex')
    )
eval6_8 (BinOp6 ex binOp ey) k =
  eval6_8
    ex
    ( \case
        Inl0 (NoOp6 vx) ->
          eval6_8
            ey
            ( \case
                Inl0 (NoOp6 vy) -> k (inj0 $ NoOp6 $ applyBinOp6 vx binOp vy)
                Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op))
                Inr0 ey' -> k (inj0 $ BinOp6 (Lit6 vx) binOp ey')
            )
        Inl0 (Op6 eff op va x_op) -> k (inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op))
        Inr0 ex' -> k (inj0 $ BinOp6 ex' binOp ey)
    )

normalise6_8 :: Expr6 -> ValueOrOp6
normalise6_8 e = eval6_8 (inj0 e) k
  where
    k (Inl0 (NoOp6 v)) = NoOp6 v
    k (Inl0 (Op6 eff op va x_op)) = Op6 eff op va x_op
    k (Inr0 e') = eval6_8 e' k

---------------------------------------------------------------
---- Step 6.9. Back to direct style
---------------------------------------------------------------
eval6_9 :: Expr6 -> ValueOrOp6 :+: Expr6
eval6_9 (Var6 nm) = error ("Free variable: " <> nm)
eval6_9 (Closed6 v) = inj0 $ NoOp6 v
eval6_9 (Lit6 v) = inj0 $ NoOp6 v
-- -------------------------------------
--    op-call op' v -> op(op, v, [])
--
--                ea -> ea'
-- -------------------------------------
--    op-call op' ea -> op-call op' ea'
--
-- -------------------------------------------------------------------
--    op-call op' op(op'',va,C[]) -> op(op'',va,op-call op' C[])
eval6_9 (OpCall6 eff op ea) =
  case eval6_9 ea of
    Inl0 (NoOp6 v) -> inj0 $ Op6 eff op v id
    Inl0 (Op6 eff' op' va x_op) -> inj0 $ Op6 eff' op' va ((\t -> OpCall6 eff op t) . x_op)
    Inr0 ea' -> inj0 (OpCall6 eff op ea')
-- --------------------------
--    let x v e -> e[x/v]
--
--          e -> e'
-- -------------------------------------
--    let x e eb -> let x e' eb
--
-- --------------------------------------------------------------
--    let x op(op',va,C[]) body -> op(op',va,let x C[] body)
eval6_9 (Let6 nm ev body) =
  case eval6_9 ev of
    Inl0 (NoOp6 v) -> eval6_9 (subst6 nm v body)
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Let6 nm t body) . x_op)
    Inr0 ev' -> inj0 (Let6 nm ev' body)
-- --------------------------------------------
--    handle {.., return x e} vb -> e[x/vb]
--
--               eb -> eb'
-- --------------------------------------------
--    handle hlr eb -> handle hlr eb'
--
-- ---------------------------------------------------------------------------------------------------
--    handle hlr@{.., op-i op' x e, ..} op(op',va,C[]) -> e[x/vb, resume/ \y -> C[y], hdl e/ handle hlr e]
eval6_9 (SHandle6 hlr@(SHandler6 eff ops (RetI6 retArgNm retBody)) seb) =
  case eval6_9 seb of
    Inl0 (NoOp6 (SuspendedV6 eb)) ->
      case eval6_9 (unSuspend eb) of
        Inl0 (NoOp6 v) -> eval6_9 (subst6 retArgNm v retBody)
        Inl0 (Op6 eff' op va x_op) ->
          if eff == eff'
            then
              let OpI6 _ param opI = fromJust $ find (\(OpI6 op' _ _) -> op == op') ops
               in eval6_9 (substHandleBody6 param va x_op hlr opI)
            else inj0 $ Op6 eff' op va (SHandle6 hlr . Lit6 . suspend6 . x_op)
        Inr0 eb' -> inj0 $ SHandle6 hlr $ Lit6 $ suspend6 eb'
    Inl0 (Op6 eff' op va x_op) -> inj0 $ Op6 eff' op va (SHandle6 hlr . x_op)
    Inr0 seb' -> inj0 $ SHandle6 hlr seb'
--
eval6_9 (If6 ec ei ee) =
  case eval6_9 ec of
    Inl0 (NoOp6 (BoolV6 c)) ->
      if c
        then eval6_9 (inj0 ei)
        else eval6_9 (inj0 ee)
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> If6 t ei ee) . x_op)
    Inr0 ec' -> inj0 $ If6 ec' ei ee
eval6_9 (App6 ef ea) =
  case eval6_9 ef of
    Inl0 (NoOp6 (LambdaV6 param f)) ->
      case eval6_9 ea of
        Inl0 (NoOp6 va) -> eval6_9 (inj0 $ subst6 param va f)
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> App6 (Lit6 (LambdaV6 param f)) t) . x_op)
        Inr0 ea' -> inj0 $ App6 (Lit6 (LambdaV6 param f)) ea'
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> App6 t ea) . x_op)
    Inr0 ef' -> inj0 $ App6 ef' ea
eval6_9 (Pair6 e1 e2) =
  case eval6_9 e1 of
    Inl0 (NoOp6 v1) ->
      case eval6_9 e2 of
        Inl0 (NoOp6 v2) -> inj0 $ NoOp6 (PairV6 v1 v2)
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Pair6 (Lit6 v1) t) . x_op)
        Inr0 e2' -> inj0 $ Pair6 (Lit6 v1) e2'
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Pair6 t e2) . x_op)
    Inr0 e1' -> inj0 $ Pair6 e1' e2
eval6_9 Nil6 = inj0 $ NoOp6 NilV6
eval6_9 (Cons6 e1 e2) =
  case eval6_9 e1 of
    Inl0 (NoOp6 v1) ->
      case eval6_9 e2 of
        Inl0 (NoOp6 v2) -> inj0 $ NoOp6 (ConsV6 v1 v2)
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Cons6 (Lit6 v1) t) . x_op)
        Inr0 e2' -> inj0 $ Cons6 (Lit6 v1) e2'
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> Cons6 t e2) . x_op)
    Inr0 e1' -> inj0 $ Cons6 e1' e2
eval6_9 (UnOp6 unOp ex) =
  case eval6_9 ex of
    Inl0 (NoOp6 vx) -> inj0 $ NoOp6 $ applyUnOp6 unOp vx
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> UnOp6 unOp t) . x_op)
    Inr0 ex' -> inj0 $ UnOp6 unOp ex'
eval6_9 (BinOp6 ex binOp ey) =
  case eval6_9 ex of
    Inl0 (NoOp6 vx) ->
      case eval6_9 ey of
        Inl0 (NoOp6 vy) -> inj0 $ NoOp6 $ applyBinOp6 vx binOp vy
        Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> BinOp6 (Lit6 vx) binOp t) . x_op)
        Inr0 ey' -> inj0 $ BinOp6 (Lit6 vx) binOp ey'
    Inl0 (Op6 eff op va x_op) -> inj0 $ Op6 eff op va ((\t -> BinOp6 t binOp ey) . x_op)
    Inr0 ex' -> inj0 $ BinOp6 ex' binOp ey

normalise6_9 :: Expr6 -> ValueOrOp6
normalise6_9 e = case eval6_9 (inj0 e) of
  Inl0 v -> v
  Inr0 e' -> error ("STUCK: " <> show e')
