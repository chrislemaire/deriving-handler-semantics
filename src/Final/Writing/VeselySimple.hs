{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Final.Writing.VeselySimple where

import Final.DTC

-- Only used for test generation, but in
-- the same place as the rest of this code.
data Type
  = IntT
  | FunT Type Type
  deriving (Show, Eq)

data Value
  = LambdaV String Expr
  | IntV Int
  deriving (Show, Eq)

data BinOpOperator = Add | Mul
  deriving (Show, Eq)

data Expr
  = Var String
  | App Expr Expr
  | Let String Expr Expr
  | BinOp Expr BinOpOperator Expr
  | Lit Value
  | Closed Value
  deriving (Show, Eq)

---------------------------------------------------------------
---- Utility for the evaler
---------------------------------------------------------------

subst :: String -> Value -> Expr -> Expr
subst x v (Var y)
  | x == y = Closed v
  | otherwise = Var y
subst x v (Lit (LambdaV y e))
  | x == y = Lit (LambdaV y e)
  | otherwise = Lit (LambdaV y (subst x v e))
subst x v (App e1 e2) = App (subst x v e1) (subst x v e2)
subst x v (Let y ev eb)
  | x == y = Let y (subst x v ev) eb
  | otherwise = Let y (subst x v ev) (subst x v eb)
subst x v (BinOp e1 op e2) = BinOp (subst x v e1) op (subst x v e2)
subst _ _ e@(Lit _) = e
subst _ _ e@(Closed _) = e

---------------------------------------------------------------
---- Step 0. The base direct-style big-step evaler
---------------------------------------------------------------
eval0 :: Expr -> Value
eval0 (Var s) = error ("Free variable: " <> s)
eval0 (App e1 e2) = case eval0 e1 of
  v1 -> case eval0 e2 of
    v2 -> case v1 of
      LambdaV x e -> eval0 (subst x v2 e)
      _ -> error ("Cannot apply non-function value: " <> show v1)
eval0 (Let x ev eb) = case eval0 ev of
  v -> eval0 (subst x v eb)
eval0 (BinOp e1 bop e2) = case eval0 e1 of
  v1 -> case eval0 e2 of
    v2 -> case (v1, bop, v2) of
      (IntV n1, Add, IntV n2) -> eval0 (Closed (IntV (n1 + n2)))
      (IntV n1, Mul, IntV n2) -> eval0 (Closed (IntV (n1 * n2)))
      _ -> error ("Cannot match types for binary operation: " <> show bop)
eval0 (Lit v) = v
eval0 (Closed v) = v

normalise0 :: Expr -> Value
normalise0 = eval0

---------------------------------------------------------------
---- Step 1. Turn direct-style into CPS
---------------------------------------------------------------
eval1 :: Expr -> (Value -> a) -> a
eval1 (Var s) _ = error ("Free variable: " <> s)
eval1 (App e1 e2) k =
  let k1 = \v1 ->
        let k2 = \v2 ->
              case v1 of
                LambdaV x e ->
                  let k' = \v -> k v
                   in eval1 (subst x v2 e) k'
                _ -> error ("Cannot apply non-function value: " <> show v1)
         in eval1 e2 k2
   in eval1 e1 k1
eval1 (Let x ev eb) k =
  let k1 = \v ->
        let k' = k
         in eval1 (subst x v eb) k'
   in eval1 ev k1
eval1 (BinOp e1 bop e2) k =
  let k1 = \v1 ->
        let k2 = \v2 ->
              case (v1, bop, v2) of
                (IntV n1, Add, IntV n2) -> eval1 (Closed (IntV (n1 + n2))) k
                (IntV n1, Mul, IntV n2) -> eval1 (Closed (IntV (n1 * n2))) k
                _ -> error ("Cannot match types for binary operation: " <> show bop)
         in eval1 e2 k2
   in eval1 e1 k1
eval1 (Lit v) k = k v
eval1 (Closed v) k = k v

normalise1 :: Expr -> Value
normalise1 = flip eval1 id

---------------------------------------------------------------
---- Step 2. Adding congruence cases where necessary
---------------------------------------------------------------
eval2 :: Expr -> (Value :+: Expr -> Value) -> Value
eval2 (Var s) _ = error ("Free variable: " <> s)
eval2 (App e1 e2) k =
  let k1 = \case
        Inl0 v1 ->
          let k2 = \case
                Inl0 v2 -> case v1 of
                  LambdaV x e -> eval2 (subst x v2 e) k
                  _ -> error ("Cannot apply non-function value: " <> show v1)
                Inr0 e2' -> eval2 e2' k2
           in eval2 e2 k2
        Inr0 e1' -> eval2 e1' k1
   in eval2 e1 k1
eval2 (Let x ev eb) k =
  let k1 = \case
        Inl0 v -> eval2 (subst x v eb) k
        Inr0 ev' -> eval2 ev' k1
   in eval2 ev k1
eval2 (BinOp e1 bop e2) k =
  let k1 = \case
        Inl0 v1 ->
          let k2 = \case
                Inl0 v2 ->
                  case (v1, bop, v2) of
                    (IntV n1, Add, IntV n2) -> eval2 (Closed (IntV (n1 + n2))) k
                    (IntV n1, Mul, IntV n2) -> eval2 (Closed (IntV (n1 * n2))) k
                    _ -> error ("Cannot match types for binary operation: " <> show bop)
                Inr0 e2' -> eval2 e2' k2
           in eval2 e2 k2
        Inr0 e1' -> eval2 e1' k1
   in eval2 e1 k1
eval2 (Lit v) k = k (inj0 v)
eval2 (Closed v) k = k (inj0 v)

normalise2 :: Expr -> Value
normalise2 e = eval2 e k
  where
    k :: Value :+: Expr -> Value
    k (Inl0 v) = v
    k (Inr0 e') = error ("STUCK: Irreducible expression: " <> show e')

---------------------------------------------------------------
---- Step 3. Argument lifting
---------------------------------------------------------------
type K3 = Value :+: Expr

eval3 :: Expr -> (K3 -> Value) -> Value
eval3 (Var s) _ = error ("Free variable: " <> s)
eval3 (App e1 e2) k =
  let k1 e2 = \case
        Inl0 v1 ->
          let k2 v1' = \case
                Inl0 v2 -> case v1' of
                  LambdaV x e -> eval3 (subst x v2 e) k
                  _ -> error ("Cannot apply non-function value: " <> show v1')
                Inr0 e2'' -> eval3 e2'' (k2 v1')
           in eval3 e2 (k2 v1)
        Inr0 e1' -> eval3 e1' (k1 e2)
   in eval3 e1 (k1 e2)
eval3 (Let x ev eb) k =
  let k1 x eb = \case
        Inl0 v -> eval3 (subst x v eb) k
        Inr0 ev' -> eval3 ev' (k1 x eb)
   in eval3 ev (k1 x eb)
eval3 (BinOp e1 bop e2) k =
  let k1 bop e2 = \case
        Inl0 v1 ->
          let k2 v1 bop = \case
                Inl0 v2 ->
                  case (v1, bop, v2) of
                    (IntV n1, Add, IntV n2) -> eval3 (Closed (IntV (n1 + n2))) k
                    (IntV n1, Mul, IntV n2) -> eval3 (Closed (IntV (n1 * n2))) k
                    _ -> error ("Cannot match types for binary operation: " <> show bop)
                Inr0 e2' -> eval3 e2' (k2 v1 bop)
           in eval3 e2 (k2 v1 bop)
        Inr0 e1' -> eval3 e1' (k1 bop e2)
   in eval3 e1 (k1 bop e2)
eval3 (Lit v) k = k (inj0 v)
eval3 (Closed v) k = k (inj0 v)

normalise3 :: Expr -> Value
normalise3 e = eval3 e k
  where
    k :: K3 -> Value
    k (Inl0 v) = v
    k (Inr0 e') = error ("STUCK: Irreducible expression: " <> show e')

---------------------------------------------------------------
---- Step 4. Continuations switch control
---------------------------------------------------------------
type K4 = Value :+: Expr

eval4 :: Expr -> (K4 -> Value) -> Value
eval4 (Var s) _ = error ("Free variable: " <> s)
eval4 (App e1 e2) k =
  let k1 e2 = \case
        Inl0 v1 ->
          let k2 v1 = \case
                Inl0 v2 -> case v1 of
                  LambdaV x e -> eval4 (subst x v2 e) k
                  _ -> error ("Cannot apply non-function value: " <> show v1)
                Inr0 e2' -> eval4 e2' (k2 v1)
           in k2 v1 (inj0 e2)
        Inr0 e1' -> eval4 e1' (k1 e2)
   in k1 e2 (inj0 e1)
eval4 (Let x ev eb) k =
  let k1 x eb = \case
        Inl0 v -> eval4 (inj0 $ subst x v eb) k
        Inr0 ev' -> eval4 ev' (k1 x eb)
   in k1 x eb (inj0 ev)
eval4 (BinOp e1 bop e2) k =
  let k1 bop e2 = \case
        Inl0 v1 ->
          let k2 v1 bop = \case
                Inl0 v2 ->
                  case (v1, bop, v2) of
                    (IntV n1, Add, IntV n2) -> eval4 (Closed (IntV (n1 + n2))) k
                    (IntV n1, Mul, IntV n2) -> eval4 (Closed (IntV (n1 * n2))) k
                    _ -> error ("Cannot match types for binary operation: " <> show bop)
                Inr0 e2' -> eval4 e2' (k2 v1 bop)
           in k2 v1 bop (inj0 e2)
        Inr0 e1' -> eval4 e1' (k1 bop e2)
   in k1 bop e2 (inj0 e1)
eval4 (Lit v) k = k (inj0 v)
eval4 (Closed v) k = k (inj0 v)

normalise4 :: Expr -> Value
normalise4 e = eval4 e k
  where
    k :: K4 -> Value
    k (Inl0 v) = v
    k (Inr0 e') = error ("STUCK: Irreducible expression: " <> show e')

---------------------------------------------------------------
---- Step 5. Defunctionalisation
---------------------------------------------------------------
data Continuation5
  = Cont5App1 Expr (Value :+: Expr)
  | Cont5App2 Value (Value :+: Expr)
  | Cont5Let1 String Expr (Value :+: Expr)
  | Cont5BinOp1 BinOpOperator Expr (Value :+: Expr)
  | Cont5BinOp2 Value BinOpOperator (Value :+: Expr)

apply5 :: Continuation5 -> ((Value :+: Expr) -> Value) -> Value
apply5 (Cont5App1 e2 e1) k = case e1 of
  Inl0 v1 -> apply5 (Cont5App2 v1 (inj0 e2)) k
  Inr0 e1' -> eval5 e1' (\e1'' -> apply5 (Cont5App1 e2 e1'') k)
apply5 (Cont5App2 v1 e2) k = case e2 of
  Inl0 v2 -> case v1 of
    LambdaV x e -> eval5 (inj0 $ subst x v2 e) k
    _ -> error ("Cannot apply non-function value: " <> show v1)
  Inr0 e2' -> eval5 e2' (\e2'' -> apply5 (Cont5App2 v1 e2'') k)
apply5 (Cont5Let1 x eb ev) k = case ev of
  Inl0 v -> eval5 (inj0 $ subst x v eb) k
  Inr0 ev' -> eval5 ev' (\ev'' -> apply5 (Cont5Let1 x eb ev'') k)
apply5 (Cont5BinOp1 bop e2 e1) k = case e1 of
  Inl0 v1 -> apply5 (Cont5BinOp2 v1 bop (inj0 e2)) k
  Inr0 e1' -> eval5 e1' (\e1'' -> apply5 (Cont5BinOp1 bop e2 e1'') k)
apply5 (Cont5BinOp2 v1 bop e2) k = case e2 of
  Inl0 v2 ->
    case (v1, bop, v2) of
      (IntV n1, Add, IntV n2) -> eval5 (Closed (IntV (n1 + n2))) k
      (IntV n1, Mul, IntV n2) -> eval5 (Closed (IntV (n1 * n2))) k
      _ -> error ("Cannot match types for binary operation: " <> show bop)
  Inr0 e2' -> eval5 e2' (\e2'' -> apply5 (Cont5BinOp2 v1 bop e2'') k)

eval5 :: Expr -> ((Value :+: Expr) -> Value) -> Value
eval5 (Var s) _ = error ("Free variable: " <> s)
eval5 (App e1 e2) k = apply5 (Cont5App1 e2 (inj0 e1)) k
eval5 (Let x ev eb) k = apply5 (Cont5Let1 x eb (inj0 ev)) k
eval5 (BinOp e1 bop e2) k = apply5 (Cont5BinOp1 bop e2 (inj0 e1)) k
eval5 (Lit v) k = k (inj0 v)
eval5 (Closed v) k = k (inj0 v)

normalise5 :: Expr -> Value
normalise5 e = eval5 (inj0 e) k
  where
    k :: (Value :+: Expr) -> Value
    k (Inl0 v) = v
    k (Inr0 e') = error ("STUCK: Irreducible expression: " <> show e')

---------------------------------------------------------------
---- Step 6. Remove tail-calls
---------------------------------------------------------------
data Continuation6
  = Cont6App1 Expr (Value :+: Expr :+: Continuation6)
  | Cont6App2 Value (Value :+: Expr :+: Continuation6)
  | Cont6Let1 String Expr (Value :+: Expr :+: Continuation6)
  | Cont6BinOp1 BinOpOperator Expr (Value :+: Expr :+: Continuation6)
  | Cont6BinOp2 Value BinOpOperator (Value :+: Expr :+: Continuation6)
  deriving (Show)

apply6 :: Continuation6 -> ((Value :+: Expr :+: Continuation6) -> Value) -> Value
apply6 (Cont6App1 e2 e1) k = case e1 of
  Inl0 v1 -> apply6 (Cont6App2 v1 (inj0 e2)) k
  Inr0 e1' -> eval6 e1' (\e1'' -> k (inj0 $ Cont6App1 e2 e1''))
apply6 (Cont6App2 v1 e2) k = case e2 of
  Inl0 v2 -> case v1 of
    LambdaV x e -> eval6 (inj0 $ subst x v2 e) k
    _ -> error ("Cannot apply non-function value: " <> show v1)
  Inr0 e2' -> eval6 e2' (\e2'' -> k (inj0 $ Cont6App2 v1 e2''))
apply6 (Cont6Let1 x eb ev) k = case ev of
  Inl0 v -> eval6 (inj0 $ subst x v eb) k
  Inr0 ev' -> eval6 ev' (\ev'' -> k (inj0 $ Cont6Let1 x eb ev''))
apply6 (Cont6BinOp1 bop e2 e1) k = case e1 of
  Inl0 v1 -> apply6 (Cont6BinOp2 v1 bop (inj0 e2)) k
  Inr0 e1' -> eval6 e1' (\e1'' -> apply6 (Cont6BinOp1 bop e2 e1'') k)
apply6 (Cont6BinOp2 v1 bop e2) k = case e2 of
  Inl0 v2 ->
    case (v1, bop, v2) of
      (IntV n1, Add, IntV n2) -> eval6 (inj0 $ Closed (IntV (n1 + n2))) k
      (IntV n1, Mul, IntV n2) -> eval6 (inj0 $ Closed (IntV (n1 * n2))) k
      _ -> error ("Cannot match types for binary operation: " <> show bop)
  Inr0 e2' -> eval6 e2' (\e2'' -> apply6 (Cont6BinOp2 v1 bop e2'') k)

eval6 :: Expr :+: Continuation6 -> ((Value :+: Expr :+: Continuation6) -> Value) -> Value
eval6 (Inr0 c) k = apply6 c k
eval6 (Inl0 (Var s)) _ = error ("Free variable: " <> s)
eval6 (Inl0 (App e1 e2)) k = apply6 (Cont6App1 e2 (inj0 e1)) k
eval6 (Inl0 (Let x ev eb)) k = apply6 (Cont6Let1 x eb (inj0 ev)) k
eval6 (Inl0 (BinOp e1 bop e2)) k = apply6 (Cont6BinOp1 bop e2 (inj0 e1)) k
eval6 (Inl0 (Lit v)) k = k (inj0 v)
eval6 (Inl0 (Closed v)) k = k (inj0 v)

normalise6 :: Expr -> Value
normalise6 e = eval6 (inj0 e) k
  where
    k :: (Value :+: Expr :+: Continuation6) -> Value
    k (Inl0 v) = v
    k (Inr0 (Inl0 e')) = error ("STUCK: Irreducible expression: " <> show e')
    k (Inr0 (Inr0 c)) = apply6 c k

---------------------------------------------------------------
---- Step 7. Convert continuations into terms
---------------------------------------------------------------
data Continuation7
  = Cont7App1 Expr (Value :+: Expr)
  | Cont7App2 Value (Value :+: Expr)
  | Cont7Let1 String Expr (Value :+: Expr)
  | Cont7BinOp1 BinOpOperator Expr (Value :+: Expr)
  | Cont7BinOp2 Value BinOpOperator (Value :+: Expr)

apply7 :: Continuation7 -> ((Value :+: Expr) -> Value) -> Value
apply7 (Cont7App1 e2 e1) k = case e1 of
  Inl0 v1 -> apply7 (Cont7App2 v1 (inj0 e2)) k
  Inr0 e1' -> eval7 e1' $ \case
    Inl0 v1 -> apply7 (Cont7App2 v1 (inj0 e2)) k
    Inr0 e1'' -> k (inj0 $ App e1'' (inj0 e2))
apply7 (Cont7App2 v1 e2) k = case e2 of
  Inl0 v2 -> case v1 of
    LambdaV x e -> eval7 (subst x v2 e) k
    _ -> error ("Cannot apply non-function value: " <> show v1)
  Inr0 e2' -> eval7 e2' $ \case
    Inl0 v2 -> case v1 of
      LambdaV x e -> eval7 (subst x v2 e) k
      _ -> error ("Cannot apply non-function value: " <> show v1)
    Inr0 e2'' -> k (inj0 $ App (Lit v1) e2'')
apply7 (Cont7Let1 x eb ev) k = case ev of
  Inl0 v -> eval7 (subst x v eb) k
  Inr0 ev' -> eval7 ev' $ \case
    Inl0 v -> eval7 (subst x v eb) k
    Inr0 ev'' -> k (inj0 $ Let x ev'' eb)
apply7 (Cont7BinOp1 bop e2 e1) k = case e1 of
  Inl0 v1 -> apply7 (Cont7BinOp2 v1 bop (inj0 e2)) k
  Inr0 e1' -> eval7 e1' $ \case
    Inl0 v1 -> apply7 (Cont7BinOp2 v1 bop (inj0 e2)) k
    Inr0 e1'' -> k (inj0 $ BinOp e1'' bop e2)
apply7 (Cont7BinOp2 v1 bop e2) k = case e2 of
  Inl0 v2 ->
    case (v1, bop, v2) of
      (IntV n1, Add, IntV n2) -> eval7 (Closed (IntV (n1 + n2))) k
      (IntV n1, Mul, IntV n2) -> eval7 (Closed (IntV (n1 * n2))) k
      _ -> error ("Cannot match types for binary operation: " <> show bop)
  Inr0 e2' -> eval7 e2' $ \case
    Inl0 v2 ->
      case (v1, bop, v2) of
        (IntV n1, Add, IntV n2) -> eval7 (Closed (IntV (n1 + n2))) k
        (IntV n1, Mul, IntV n2) -> eval7 (Closed (IntV (n1 * n2))) k
        _ -> error ("Cannot match types for binary operation: " <> show bop)
    Inr0 e2'' -> k (inj0 $ BinOp (Lit v1) bop e2'')

eval7 :: Expr -> ((Value :+: Expr) -> Value) -> Value
eval7 (Var s) _ = error ("Free variable: " <> s)
eval7 (App e1 e2) k = apply7 (Cont7App1 e2 (inj0 e1)) k
eval7 (Let x ev eb) k = apply7 (Cont7Let1 x eb (inj0 ev)) k
eval7 (BinOp e1 bop e2) k = apply7 (Cont7BinOp1 bop e2 (inj0 e1)) k
eval7 (Lit v) k = k (inj0 v)
eval7 (Closed v) k = k (inj0 v)

normalise7 :: Expr -> Value
normalise7 e = eval7 e k
  where
    k :: (Value :+: Expr) -> Value
    k (Inl0 v) = v
    k (Inr0 e') = error ("STUCK: Irreducible expression: " <> show e')

---------------------------------------------------------------
---- Step 8. Inlining and simplification
---------------------------------------------------------------
eval8 :: Expr -> ((Value :+: Expr) -> Value) -> Value
eval8 (Var s) _ = error ("Free variable: " <> s)
eval8 (App e1 e2) k = eval8 e1 $ \case
  Inl0 v1 -> eval8 e2 $ \case
    Inl0 v2 -> case v1 of
      LambdaV x e -> eval8 (subst x v2 e) k
      _ -> error ("Cannot apply non-function value: " <> show v1)
    Inr0 e2' -> k (inj0 $ App (Lit v1) e2')
  Inr0 e1' -> k (inj0 $ App e1' (inj0 e2))
eval8 (Let x ev eb) k = eval8 ev $ \case
  Inl0 v -> eval8 (subst x v eb) k
  Inr0 ev' -> k (inj0 $ Let x ev' eb)
eval8 (BinOp e1 bop e2) k = eval8 e1 $ \case
  Inl0 v1 -> eval8 e2 $ \case
    Inl0 v2 ->
      case (v1, bop, v2) of
        (IntV n1, Add, IntV n2) -> eval8 (Closed (IntV (n1 + n2))) k
        (IntV n1, Mul, IntV n2) -> eval8 (Closed (IntV (n1 * n2))) k
        _ -> error ("Cannot match types for binary operation: " <> show bop)
    Inr0 e2' -> k (inj0 $ BinOp (Lit v1) bop e2')
  Inr0 e1' -> k (inj0 $ BinOp e1' bop e2)
eval8 (Lit v) k = k (inj0 v)
eval8 (Closed v) k = k (inj0 v)

normalise8 :: Expr -> Value
normalise8 e = eval8 e k
  where
    k :: (Value :+: Expr) -> Value
    k (Inl0 v) = v
    k (Inr0 e') = error ("STUCK: Irreducible expression: " <> show e')

---------------------------------------------------------------
---- Step 9. Back to direct style
---------------------------------------------------------------
eval9 :: Expr -> (Value :+: Expr)
eval9 (Var s) = error ("Free variable: " <> s)
eval9 (App e1 e2) = case eval9 e1 of
  Inl0 v1 -> case eval9 e2 of
    Inl0 v2 -> case v1 of
      LambdaV x e -> eval9 (subst x v2 e)
      _ -> error ("Cannot apply non-function value: " <> show v1)
    Inr0 e2' -> inj0 $ App (Lit v1) e2'
  Inr0 e1' -> inj0 $ App e1' (inj0 e2)
eval9 (Let x ev eb) = case eval9 ev of
  Inl0 v -> eval9 (subst x v eb)
  Inr0 ev' -> inj0 $ Let x ev' eb
eval9 (BinOp e1 bop e2) = case eval9 e1 of
  Inl0 v1 -> case eval9 e2 of
    Inl0 v2 ->
      case (v1, bop, v2) of
        (IntV n1, Add, IntV n2) -> eval9 (Closed (IntV (n1 + n2)))
        (IntV n1, Mul, IntV n2) -> eval9 (Closed (IntV (n1 * n2)))
        _ -> error ("Cannot match types for binary operation: " <> show bop)
    Inr0 e2' -> inj0 $ BinOp (Lit v1) bop e2'
  Inr0 e1' -> inj0 $ BinOp e1' bop e2
eval9 (Lit v) = inj0 v
eval9 (Closed v) = inj0 v

normalise9 :: Expr -> Value
normalise9 e = case eval9 e of
  Inl0 v -> v
  Inr0 e' -> error ("STUCK: Irreducible expression: " <> show e')
