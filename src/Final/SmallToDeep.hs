{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Final.SmallToDeep where

import Data.List (find)
import Final.DTC
import Control.Monad (ap, liftM)


-- For deriving shows easily
instance Show (a -> b) where
  show _ = "<func>"

-- Values, including value types needed to demonstrate evaler capabilities
data Value
  = LambdaV String Expr
  | IntV Int
  | BoolV Bool
  | UnitV
  | PairV Value Value
  | NilV
  | ConsV Value Value
  deriving (Show, Eq)

data OpI = OpI String String String Expr
  deriving (Show, Eq)
data ReturnI = ReturnI String Expr
  deriving (Show, Eq)
data Handler = Handler [OpI] ReturnI
  deriving (Show, Eq)

data UnOpOperator = Fst | Snd
  deriving (Show, Eq)
data BinOpOperator = Add | Mul | Concat
  deriving (Show, Eq)

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr
  = Var String
  | App Expr Expr
  | Let String Expr Expr
  | OpCall String Expr
  | Handle Handler Expr
  | Lit Value
  | Closed Value

  | If Expr Expr Expr
  | Pair Expr Expr
  | Cons Expr Expr
  | UnOp UnOpOperator Expr
  | BinOp Expr BinOpOperator Expr
  deriving (Show, Eq)

do' :: [(Maybe String, Expr)] -> Expr -> Expr
do' []                  res = res
do' ((Nothing, eb) : t) res = Let "_" eb (do' t res)
do' ((Just nm, eb) : t) res = Let nm  eb (do' t res)

-- Smart constructors for values and resume functionality
lambda :: String -> Expr -> Expr
lambda x eb = Lit (LambdaV x eb)

int :: Int -> Expr
int = Lit . IntV

unit :: Expr
unit = Lit UnitV

resume :: Expr -> Expr
resume = App (Var "resume")

list :: [Expr] -> Expr
list [] = Lit NilV
list (e:es) = Cons e (list es)

-- Example handlers
hSt :: Expr -> Expr -> Expr
hSt st e = App (Handle (Handler
  [OpI "get" "_" "resume" (lambda "s" (App (resume (Var "s")) (Var "s"))),
   OpI "put" "s'" "resume" (lambda "s" (App (resume unit) (Var "s'")))]
  (ReturnI "x" (lambda "s" (Pair (Var "s") (Var "x")))))
  e) st


-- put :: s -> (s -> f ())

data St s a where
  Put :: s -> St s ()

--handler {
--  get(s) --> s
--}

hAmb :: Expr -> Expr
hAmb = Handle (Handler
  [OpI "1or2" "()" "resume" (BinOp (resume (int 1)) Concat (resume (int 2)))]
  (ReturnI "x" (list [Var "x"])))

-- Example program
pStAmb :: Expr
pStAmb =
  Let "j" (OpCall "1or2" unit) $
  Let "i" (OpCall "get" unit) $
  Let "_" (OpCall "put" (BinOp (Var "i") Add (int 1))) $
  BinOp (Var "i") Mul (Var "j")

-- Potential reductions, including those necessary to work through binary operations
data PotentialRedex
  = PRBeta String Expr Value
  | PRLet String Expr Value
  | PRHandleReturn String Expr Value
  | PRHandleOp Handler (Expr -> Expr) String String Expr Value
  | PRIf Value Expr Expr
  | PRError String
  -- Constructor for BinOp reductions left out
  | PRUnOp UnOpOperator Value
  | PRBinOp Value BinOpOperator Value
  deriving (Show)

data ContractumOrError
  = Contractum Expr
  | Error String
  deriving (Show)

substOp :: String -> Value -> OpI -> OpI
substOp x v (OpI op y k e)
  | x == y || x == k = OpI op y k e
  | otherwise = OpI op y k (subst x v e)

substV :: String -> Value -> Value -> Value
substV x v (PairV v1 v2) = PairV (substV x v v1) (substV x v v2)
substV x v (LambdaV y body)
  | x == y = LambdaV y body
  | otherwise = LambdaV y (subst x v body)
substV x v (ConsV v1 v2) = ConsV (substV x v v1) (substV x v v2)
substV _ _ vv = vv

subst :: String -> Value -> Expr -> Expr
subst x v (Var y)
  | x == y = Closed v
  | otherwise = Var y
subst x v (Lit vv) = Lit (substV x v vv)
subst x v (App ef ea) = App (subst x v ef) (subst x v ea)
subst x v (Let y ev eb)
  | x == y = Let y (subst x v ev) eb
  | otherwise = Let y (subst x v ev) (subst x v eb)
subst x v (If ec et ee) = If (subst x v ec) (subst x v et) (subst x v ee)
subst x v (OpCall op e) = OpCall op (subst x v e)
subst x v (Handle (Handler ops (ReturnI y er)) e) =
  Handle (Handler (substOp x v <$> ops)
                  (if x == y then ReturnI y er else ReturnI y (subst x v er)))
         (subst x v e)
subst _ _ e@(Closed _) = e
-- Cases for Pair, List, and BinOp left out
subst x v (Pair e1 e2) = Pair (subst x v e1) (subst x v e2)
subst x v (Cons e1 e2) = Cons (subst x v e1) (subst x v e2)
subst x v (UnOp op e) = UnOp op (subst x v e)
subst x v (BinOp e1 op e2) = BinOp (subst x v e1) op (subst x v e2)

concatListVs :: Value -> Value -> Maybe Value
concatListVs NilV NilV = Just NilV
concatListVs NilV vs' = Just vs'
concatListVs vs NilV = Just vs
concatListVs (ConsV v vs) vs' = ConsV v <$> (concatListVs vs vs')
concatListVs _ _ = Nothing

contract :: PotentialRedex -> ContractumOrError
contract (PRBeta x eb v) = Contractum (subst x v eb)
contract (PRLet x eb v) = Contractum (subst x v eb)
contract (PRHandleReturn x er v) = Contractum (subst x v er)
contract (PRHandleOp h x_op x k eop v) = Contractum (subst x v
  (subst k (LambdaV "y" (Handle h (x_op (Var "y")))) eop))
contract (PRIf (BoolV b) et ee) = Contractum (if b then et else ee)
contract (PRIf v _ _) = Error ("If condition is not a boolean: " <> show v)
contract (PRError err) = Error err
-- Cases for binary operations left out
contract (PRUnOp Fst (PairV v1 _)) = Contractum (Closed v1)
contract (PRUnOp Snd (PairV _ v2)) = Contractum (Closed v2)
contract (PRUnOp uop _) = Error ("Cannot match types for un-op: " <> show uop)
contract (PRBinOp l1 Concat l2) = maybe
  (Error ("Cannot match types for bin-op: " <> show Concat)) (Contractum . Closed)
  (concatListVs l1 l2)
contract (PRBinOp (IntV n1) Add (IntV n2)) = Contractum (Closed (IntV (n1 + n2)))
contract (PRBinOp (IntV n1) Mul (IntV n2)) = Contractum (Closed (IntV (n1 * n2)))
contract (PRBinOp _ bop _) = Error ("Cannot match types for bin-op: " <> show bop)

data Context
  = CEmpty
  | CAppL Context Expr | CAppR Value Context
  | CLet String Context Expr
  | COp String Context
  | CHandle Handler Context
  | CIf Context Expr Expr
  -- Constructors for List, Pair, and BinOp contexts left out
  | CConsL Context Expr | CConsR Value Context
  | CPairL Context Expr | CPairR Value Context
  | CUnOp UnOpOperator Context
  | CBinOpL Context BinOpOperator Expr | CBinOpR Value BinOpOperator Context
  deriving (Show)

recompose_ss :: Context -> (Context, Expr -> Expr)
recompose_ss (CAppL c ea) = (c, \t ->  App t ea)
recompose_ss (CAppR vf c) = (c, \t ->  App (Closed vf) t)
recompose_ss (CLet x c eb) = (c, \t ->  Let x t eb)
recompose_ss (COp op c) = (c, \t ->  OpCall op t)
recompose_ss (CHandle h c) = (c, \t ->  Handle h t)
recompose_ss (CIf c et ee) = (c, \t ->  If t et ee)
-- Cases for recomposing List, Pair, and BinOp contexts left out
recompose_ss (CConsL c es) = (c, \t ->  Cons t es)
recompose_ss (CConsR v c) = (c, \t ->  Cons (Closed v) t)
recompose_ss (CPairL c e2) = (c, \t -> Pair t e2)
recompose_ss (CPairR v1 c) = (c, \t -> Pair (Closed v1) t)
recompose_ss (CUnOp uop c) = (c, \t -> UnOp uop t)
recompose_ss (CBinOpL c bop e2) = (c, \t -> BinOp t bop e2)
recompose_ss (CBinOpR v1 bop c) = (c, \t -> BinOp (Closed v1) bop t)


data ValueOrDecomposition
  = VODValue Value
  | VODDec PotentialRedex Context
  deriving (Show)

data ValueOrOp
  = NoOp Value
  | Op String Value (Expr -> Expr)

--decompose_expr0 :: Context -> Expr -> ValueOrDecomposition
--decompose_expr0 c (Var s) = VODDec (PRError ("Free variable: " <> s)) c
--decompose_expr0 c (App ef ea) = decompose_expr0 (CAppL c e2) e1
--decompose_expr0 c (Let x ev eb) = decompose_expr0 (CLet x c eb) ev
--decompose_expr0 c (OpCall op e) = decompose_expr0 (COp op c) e
--decompose_expr0 c (Handle h eb) = decompose_expr0 (CHandle h c) eb
--decompose_expr0 c (Lit v) = decompose_context0 (NoOp v) c
--decompose_expr0 c (Closed v) = decompose_context0 (NoOp v) c
---- Cases for List, Pair, and BinOp left out
--decompose_expr0 c (List []) = decompose_context0 (NoOp (ListV [])) c
--decompose_expr0 c (List (e : es)) = decompose_expr0 (CList [] c es) e
--decompose_expr0 c (Pair e1 e2) = decompose_expr0 (CPairL c e2) e1
--decompose_expr0 c (BinOp e1 bop e2) = decompose_expr0 (CBinOpL c bop e2) e1
--
--decompose_context0 :: ValueOrOp -> Context -> ValueOrDecomposition
--decompose_context0 (NoOp v) CEmpty = VODValue v
--decompose_context0 (Op op v _) CEmpty =
--  VODDec (PRError ("Cannot handle free op: " <> op <> "(" <> show v <> ")")) CEmpty
--decompose_context0 (NoOp v) (CAppL c e2) = decompose_expr0 (CAppR v c) e2
--decompose_context0 (Op op v x_op) (CAppL c e2) =
--  decompose_context0 (Op op v (\t -> App (x_op t) e2)) c
--decompose_context0 (NoOp v) (CAppR (LambdaV x e) c) = VODDec (PRBeta x e v) c
--decompose_context0 (NoOp _) (CAppR v1 c) =
--  VODDec (PRError ("Cannot apply non-function value: " <> show v1)) c
--decompose_context0 (Op op v x_op) (CAppR v1 c) =
--  decompose_context0 (Op op v (\t -> App (Lit v1) (x_op t))) c
--decompose_context0 (NoOp v) (CLet x c eb) = VODDec (PRLet x eb v) c
--decompose_context0 (Op op v x_op) (CLet x c eb) =
--  decompose_context0 (Op op v (\t -> Let x (x_op t) eb)) c
--decompose_context0 (NoOp v) (COp op c) = decompose_context0 (Op op v id) c
--decompose_context0 (Op op v x_op) (COp op' c) =
--  decompose_context0 (Op op v (\t -> OpCall op' (x_op t))) c
--decompose_context0 (NoOp v) (CHandle (Handler _ (ReturnI x e)) c) = VODDec (PRHandleReturn x e v) c
--decompose_context0 (Op op v x_op) (CHandle h@(Handler ops _) c) =
--  case find (\(OpI op' _ _) -> op == op') ops of
--    Just (OpI _ x e) -> VODDec (PRHandleOp h x_op x e v) c
--    Nothing -> decompose_context0 (Op op v (\t -> Handle h (x_op t))) c
---- Cases for List, Pair, and BinOp contexts left out
--decompose_context0 (NoOp v) (CList vs c []) = decompose_context0 (NoOp (ListV (vs <> [v]))) c
--decompose_context0 (NoOp v) (CList vs c (e : es)) = decompose_expr0 (CList (vs <> [v]) c es) e
--decompose_context0 (Op op v x_op) (CList vs c es) =
--  decompose_context0 (Op op v (\t -> List ((Closed <$> vs) <> ((x_op t) : es)))) c
--decompose_context0 (NoOp v1) (CPairL c e2) = decompose_expr0 (CPairR v1 c) e2
--decompose_context0 (Op op v x_op) (CPairL c e2) =
--  decompose_context0 (Op op v (\t -> Pair (x_op t) e2)) c
--decompose_context0 (NoOp v2) (CPairR v1 c) = decompose_context0 (NoOp (PairV v1 v2)) c
--decompose_context0 (Op op v x_op) (CPairR v1 c) =
--  decompose_context0 (Op op v (\t -> Pair (Closed v1) (x_op t))) c
--decompose_context0 (NoOp v1) (CBinOpL c bop e2) = decompose_expr0 (CBinOpR v1 bop c) e2
--decompose_context0 (Op op v x_op) (CBinOpL c bop e2) =
--  decompose_context0 (Op op v (\t -> BinOp (x_op t) bop e2)) c
--decompose_context0 (NoOp v2) (CBinOpR v1 bop c) = VODDec (PRBinOp v1 bop v2) c
--decompose_context0 (Op op v x_op) (CBinOpR v1 bop c) =
--  decompose_context0 (Op op v (\t -> BinOp (Closed v1) bop (x_op t))) c
--
--decompose0 :: Expr -> ValueOrDecomposition
--decompose0 = decompose_expr0 CEmpty

data Result
  = Result Value
  | Wrong String
  deriving (Show, Eq)

--iterate0 :: ValueOrDecomposition -> Result
--iterate0 (VODValue v) = Result v
--iterate0 (VODDec pr c) = case contract pr of
--  Contractum e -> iterate0 (decompose0 (recompose c e))
--  Error err -> Wrong err
--
--normalise0 :: Expr -> Result
--normalise0 e = iterate0 (decompose0 e)




decompose_expr :: Context -> Expr -> ValueOrDecomposition
decompose_expr c (Var s) = VODDec (PRError ("Free variable: " <> s)) c
decompose_expr c (App ef ea) = decompose_expr (CAppL c ea) ef
decompose_expr c (Let x ev eb) = decompose_expr (CLet x c eb) ev
decompose_expr c (OpCall op e) = decompose_expr (COp op c) e
decompose_expr c (Handle h eb) = decompose_expr (CHandle h c) eb
decompose_expr c (If ec et ee) = decompose_expr (CIf c et ee) ec
decompose_expr c (Lit v) = decompose_context v c
decompose_expr c (Closed v) = decompose_context v c
-- Cases for List, Pair, and BinOp left out
decompose_expr c (Cons e es) = decompose_expr (CConsL c es) e
decompose_expr c (Pair e1 e2) = decompose_expr (CPairL c e2) e1
decompose_expr c (UnOp uop e) = decompose_expr (CUnOp uop c) e
decompose_expr c (BinOp e1 bop e2) = decompose_expr (CBinOpL c bop e2) e1

recompose :: Context -> Expr -> Expr
recompose CEmpty t = t
recompose c t = let (c', f) = recompose_ss c in recompose c' (f t)

recompose_op :: String -> Value -> (Expr -> Expr) -> Context -> ValueOrDecomposition
recompose_op op v _ CEmpty =
  VODDec (PRError ("Cannot handle free op: " <> op <> "(" <> show v <> ")")) CEmpty
recompose_op op v x_op c@(CHandle h@(Handler ops _) c') =
  case find (\(OpI op' _ _ _) -> op == op') ops of
    Just (OpI _ x k e) -> VODDec (PRHandleOp h x_op x k e v) c'
    Nothing ->
      let (_, f) = recompose_ss c
      in recompose_op op v (f . x_op) c'
recompose_op op v x_op c =
  let (c', f) = recompose_ss c
  in recompose_op op v (f . x_op) c'


-- recompose_op :: String -> Value -> (Expr -> Expr) -> Context -> ValueOrDecomposition
-- recompose_op op v _ CEmpty = VODDec (PRError ("Cannot handle free op: " <> op <> "(" <> show v <> ")")) CEmpty
-- --recompose_op (CAppL c e2) x_op t = App (x_op t) e2
-- --recompose_op (CAppL c e2) x_op = (\t -> App t e2) . x_op
-- --recompose_op (CAppL c e2) = (c, \t -> App t e2)
-- recompose_op op v x_op (CAppL c e2) = recompose_op op v ((\t -> App t e2) . x_op) c
-- recompose_op op v x_op (CAppR v1 c) = recompose_op op v ((\t -> App (Closed v1) t) . x_op) c
-- recompose_op op v x_op (CLet x c eb) = recompose_op op v ((\t -> Let x t eb) . x_op) c
-- recompose_op op v x_op (COp op' c) = recompose_op op v ((\t -> OpCall op' t) . x_op) c
-- recompose_op op v x_op (CHandle h@(Handler ops _) c) =
--   case find (\(OpI op' _ _ _) -> op == op') ops of
--     Just (OpI _ x k e) -> VODDec (PRHandleOp h x_op x k e v) c
--     Nothing -> recompose_op op v ((\t -> Handle h t) . x_op) c
-- recompose_op op v x_op (CIf c et ee) = recompose_op op v ((\t -> If t et ee) . x_op) c
-- -- Cases for List, Pair, and BinOp are left out
-- recompose_op op v x_op (CConsL c es) = recompose_op op v ((\t -> Cons t es) . x_op) c
-- recompose_op op v x_op (CConsR vh c) = recompose_op op v ((\t -> Cons (Closed vh) t) . x_op) c
-- recompose_op op v x_op (CPairL c e2) = recompose_op op v ((\t -> Pair t e2) . x_op) c
-- recompose_op op v x_op (CPairR v1 c) = recompose_op op v ((\t -> Pair (Closed v1) t) . x_op) c
-- recompose_op op v x_op (CUnOp uop c) = recompose_op op v ((\t -> UnOp uop t) . x_op) c
-- recompose_op op v x_op (CBinOpL c bop e2) = recompose_op op v ((\t -> BinOp t bop e2) . x_op) c
-- recompose_op op v x_op (CBinOpR v1 bop c) = recompose_op op v ((\t -> BinOp (Closed v1) bop t) . x_op) c

decompose_context :: Value -> Context -> ValueOrDecomposition
decompose_context v CEmpty = VODValue v
decompose_context v (CAppL c ea) = decompose_expr (CAppR v c) ea
decompose_context v (CAppR (LambdaV x eb) c) = VODDec (PRBeta x eb v) c
decompose_context _ (CAppR vf c) =
  VODDec (PRError ("Cannot apply non-function value: " <> show vf)) c
decompose_context v (CLet x c eb) = VODDec (PRLet x eb v) c
decompose_context v (COp op c) = recompose_op op v id c
decompose_context v (CHandle (Handler _ (ReturnI x e)) c) = VODDec (PRHandleReturn x e v) c
decompose_context v (CIf c et ee) = VODDec (PRIf v et ee) c
-- Cases for List, Pair, and BinOp contexts left out
decompose_context v (CConsL c es) = decompose_expr (CConsR v c) es
decompose_context vs (CConsR v c) = decompose_context (ConsV v vs) c
decompose_context v1 (CPairL c e2) = decompose_expr (CPairR v1 c) e2
decompose_context v2 (CPairR v' c) = decompose_context (PairV v' v2) c
decompose_context v (CUnOp uop c) = VODDec (PRUnOp uop v) c
decompose_context v1 (CBinOpL c bop e2) = decompose_expr (CBinOpR v1 bop c) e2
decompose_context v2 (CBinOpR v' bop c) = VODDec (PRBinOp v' bop v2) c


decompose :: Expr -> ValueOrDecomposition
decompose = decompose_expr CEmpty

data Reduct
  = RResult Value
  | RExpr Expr
  | RError String
  deriving Show

reduce0 :: Int -> ValueOrDecomposition -> Reduct
reduce0 _ (VODValue v) = RResult v
reduce0 n (VODDec pr c) = case contract pr of
  Contractum e -> if n == 0
    then RExpr (recompose c e)
    else reduce0 (n - 1) (decompose (recompose c e))
  Error err -> RError err

reduceTo :: Int -> Expr -> Reduct
reduceTo n = reduce0 n . decompose

iterate0 :: ValueOrDecomposition -> Result
iterate0 (VODValue v) = Result v
iterate0 (VODDec pr c) = case contract pr of
  Contractum e -> iterate0 (decompose (recompose c e))
  Error err -> Wrong err

normalise0 :: Expr -> Result
normalise0 e = iterate0 (decompose e)




refocus :: Context -> Expr -> ValueOrDecomposition
refocus = decompose_expr

iterate1 :: ValueOrDecomposition -> Result
iterate1 (VODValue v) = Result v
iterate1 (VODDec pr c) = case contract pr of
  Contractum e -> iterate1 (refocus c e)
  Error err -> Wrong err

normalise1 :: Expr -> Result
normalise1 e = iterate1 (decompose e)




iterate2 :: ValueOrDecomposition -> Result
iterate2 (VODValue v) = Result v
iterate2 (VODDec (PRBeta x e v) c) = iterate2 $ refocus c (subst x v e)
iterate2 (VODDec (PRLet x e v) c) = iterate2 $ refocus c (subst x v e)
iterate2 (VODDec (PRHandleReturn x e v) c) = iterate2 $ refocus c (subst x v e)
iterate2 (VODDec (PRHandleOp h x_op x k e v) c) = iterate2 $ refocus c (subst x v
  (subst k (LambdaV "y" (Handle h (x_op (Var "y")))) e))
iterate2 (VODDec (PRIf (BoolV b) et ee) c) = iterate2 $ refocus c (if b then et else ee)
iterate2 (VODDec (PRIf v _ _) _) = Wrong ("If condition is not a boolean: " <> show v)
iterate2 (VODDec (PRError err) _) = Wrong err
-- Cases for BinOp left out
iterate2 (VODDec (PRUnOp Fst (PairV v1 _)) c) = iterate2 $ refocus c (Closed v1)
iterate2 (VODDec (PRUnOp Snd (PairV _ v2)) c) = iterate2 $ refocus c (Closed v2)
iterate2 (VODDec (PRUnOp uop _) _) = Wrong ("Cannot match types for un-op: " <> show uop)
iterate2 (VODDec (PRBinOp l1 Concat l2) c) = maybe
  (Wrong ("Cannot match types for bin-op: " <> show Concat)) (iterate2 . refocus c . Closed)
  (concatListVs l1 l2)
iterate2 (VODDec (PRBinOp (IntV n1) Add (IntV n2)) c) = iterate2 $ refocus c (Closed (IntV (n1 + n2)))
iterate2 (VODDec (PRBinOp (IntV n1) Mul (IntV n2)) c) = iterate2 $ refocus c (Closed (IntV (n1 * n2)))
iterate2 (VODDec (PRBinOp _ bop _) _) = Wrong ("Cannot match types for bin-op: " <> show bop)

normalise2 :: Expr -> Result
normalise2 = iterate2 . refocus CEmpty






refocus_expr3 :: Context -> Expr -> Result
refocus_expr3 c (Var s) = iterate3 $ VODDec (PRError ("Free variable: " <> s)) c
refocus_expr3 c (App ef ea) = refocus_expr3 (CAppL c ea) ef
refocus_expr3 c (Let x ev eb) = refocus_expr3 (CLet x c eb) ev
refocus_expr3 c (OpCall op e) = refocus_expr3 (COp op c) e
refocus_expr3 c (Handle h eb) = refocus_expr3 (CHandle h c) eb
refocus_expr3 c (If ec et ee) = refocus_expr3 (CIf c et ee) ec
refocus_expr3 c (Lit v) = refocus_context3 v c
refocus_expr3 c (Closed v) = refocus_context3 v c
-- Cases for List, Pair, and BinOp left out
refocus_expr3 c (Cons e es) = refocus_expr3 (CConsL c es) e
refocus_expr3 c (Pair e1 e2) = refocus_expr3 (CPairL c e2) e1
refocus_expr3 c (UnOp uop e) = refocus_expr3 (CUnOp uop c) e
refocus_expr3 c (BinOp e1 bop e2) = refocus_expr3 (CBinOpL c bop e2) e1

refocus_context3 :: Value -> Context -> Result
refocus_context3 v CEmpty = iterate3 $ VODValue v
refocus_context3 v (CAppL c ea) = refocus_expr3 (CAppR v c) ea
refocus_context3 v (CAppR (LambdaV x eb) c) = iterate3 $ VODDec (PRBeta x eb v) c
refocus_context3 _ (CAppR vf c) =
  iterate3 $ VODDec (PRError ("Cannot apply non-function value: " <> show vf)) c
refocus_context3 v (CLet x c eb) = iterate3 $ VODDec (PRLet x eb v) c
refocus_context3 v (COp op c) = refocus_op3 op v id c
refocus_context3 v (CHandle (Handler _ (ReturnI x e)) c) = iterate3 $ VODDec (PRHandleReturn x e v) c
refocus_context3 v (CIf c et ee) = iterate3 $ VODDec (PRIf v et ee) c
-- Cases for List, Pair, and BinOp contexts left out
refocus_context3 v (CConsL c es) = refocus_expr3 (CConsR v c) es
refocus_context3 vs (CConsR v c) = refocus_context3 (ConsV v vs) c
refocus_context3 v1 (CPairL c e2) = refocus_expr3 (CPairR v1 c) e2
refocus_context3 v2 (CPairR v1 c) = refocus_context3 (PairV v1 v2) c
refocus_context3 v (CUnOp uop c) = iterate3 $ VODDec (PRUnOp uop v) c
refocus_context3 v1 (CBinOpL c bop e2) = refocus_expr3 (CBinOpR v1 bop c) e2
refocus_context3 v2 (CBinOpR v1 bop c) = iterate3 $ VODDec (PRBinOp v1 bop v2) c

refocus_op3 :: String -> Value -> (Expr -> Expr) -> Context -> Result
refocus_op3 op v _ CEmpty =
  iterate3 $ VODDec (PRError ("Cannot handle free op: " <> op <> "(" <> show v <> ")")) CEmpty
refocus_op3 op v x_op c@(CHandle h@(Handler ops _) c') =
  case find (\(OpI op' _ _ _) -> op == op') ops of
    Just (OpI _ x k e) -> iterate3 $ VODDec (PRHandleOp h x_op x k e v) c'
    Nothing ->
      let (_, f) = recompose_ss c
      in refocus_op3 op v (f . x_op) c'
refocus_op3 op v x_op c =
  let (c', f) = recompose_ss c
  in refocus_op3 op v (f . x_op) c'

iterate3 :: ValueOrDecomposition -> Result
iterate3 (VODValue v) = Result v
iterate3 (VODDec (PRBeta x e v) c) = refocus_expr3 c (subst x v e)
iterate3 (VODDec (PRLet x e v) c) = refocus_expr3 c (subst x v e)
iterate3 (VODDec (PRHandleReturn x e v) c) = refocus_expr3 c (subst x v e)
iterate3 (VODDec (PRHandleOp h x_op x k e v) c) = refocus_expr3 c (subst x v
  (subst k (LambdaV "y" (Handle h (x_op (Var "y")))) e))
iterate3 (VODDec (PRIf (BoolV b) et ee) c) = refocus_expr3 c (if b then et else ee)
iterate3 (VODDec (PRIf v _ _) _) = Wrong ("If condition is not a boolean: " <> show v)
iterate3 (VODDec (PRError err) _) = Wrong err
-- Cases for BinOp left out
iterate3 (VODDec (PRUnOp Fst (PairV v1 _)) c) = refocus_expr3 c (Closed v1)
iterate3 (VODDec (PRUnOp Snd (PairV _ v2)) c) = refocus_expr3 c (Closed v2)
iterate3 (VODDec (PRUnOp uop _) _) = Wrong ("Cannot match types for un-op: " <> show uop)
iterate3 (VODDec (PRBinOp l1 Concat l2) c) = maybe
  (Wrong ("Cannot match types for bin-op: " <> show Concat)) (refocus_expr3 c . Closed)
  (concatListVs l1 l2)
iterate3 (VODDec (PRBinOp (IntV n1) Add (IntV n2)) c) = refocus_expr3 c (Closed (IntV (n1 + n2)))
iterate3 (VODDec (PRBinOp (IntV n1) Mul (IntV n2)) c) = refocus_expr3 c (Closed (IntV (n1 * n2)))
iterate3 (VODDec (PRBinOp _ bop _) _) = Wrong ("Cannot match types for bin-op: " <> show bop)

normalise3 :: Expr -> Result
normalise3 = refocus_expr3 CEmpty





refocus_expr4 :: Context -> Expr -> Result
refocus_expr4 _ (Var s) = Wrong ("Free variable: " <> s)
refocus_expr4 c (App ef ea) = refocus_expr4 (CAppL c ea) ef
refocus_expr4 c (Let x ev eb) = refocus_expr4 (CLet x c eb) ev
refocus_expr4 c (OpCall op e) = refocus_expr4 (COp op c) e
refocus_expr4 c (Handle h eb) = refocus_expr4 (CHandle h c) eb
refocus_expr4 c (If ec et ee) = refocus_expr4 (CIf c et ee) ec
refocus_expr4 c (Lit v) = refocus_context4 (NoOp v) c
refocus_expr4 c (Closed v) = refocus_context4 (NoOp v) c
-- Cases for List, Pair, and BinOp left out
refocus_expr4 c (Cons e es) = refocus_expr4 (CConsL c es) e
refocus_expr4 c (Pair e1 e2) = refocus_expr4 (CPairL c e2) e1
refocus_expr4 c (UnOp uop e) = refocus_expr4 (CUnOp uop c) e
refocus_expr4 c (BinOp e1 bop e2) = refocus_expr4 (CBinOpL c bop e2) e1

refocus_context4 :: ValueOrOp -> Context -> Result
refocus_context4 (NoOp v) CEmpty = Result v
refocus_context4 (Op op v _) CEmpty =
  Wrong ("Cannot handle free op: " <> op <> "(" <> show v <> ")")
refocus_context4 (Op op v x_op) c@(CHandle h@(Handler ops _) c') =
  case find (\(OpI op' _ _ _) -> op == op') ops of
    Just (OpI _ x k e) ->
      refocus_expr4 c' (subst x v
                       (subst k (LambdaV "y" (Handle h (x_op (Var "y"))))
                        e))
    Nothing ->
      let (_, f) = recompose_ss c
      in refocus_context4 (Op op v (f . x_op)) c'
refocus_context4 (Op op v x_op) c =
  let (c', f) = recompose_ss c
  in refocus_context4 (Op op v (f . x_op)) c'
refocus_context4 (NoOp v) (CAppL c ea) = refocus_expr4 (CAppR v c) ea
refocus_context4 (NoOp v) (CAppR (LambdaV x eb) c) = refocus_expr4 c (subst x v eb)
refocus_context4 (NoOp _) (CAppR vf _) =
  Wrong ("Cannot apply non-function value: " <> show vf)
refocus_context4 (NoOp v) (CLet x c eb) = refocus_expr4 c (subst x v eb)
refocus_context4 (NoOp (BoolV b)) (CIf c et ee) = refocus_expr4 c (if b then et else ee)
refocus_context4 (NoOp v) (CIf _ _ _) = Wrong ("If condition is not a boolean: " <> show v)
refocus_context4 (NoOp v) (COp op c) = refocus_context4 (Op op v id) c
refocus_context4 (NoOp v) (CHandle (Handler _ (ReturnI x e)) c) = refocus_expr4 c (subst x v e)
-- Cases for List, Pair, and BinOp contexts left out
refocus_context4 (NoOp v) (CConsL c es) = refocus_expr4 (CConsR v c) es
refocus_context4 (NoOp vs) (CConsR v c) = refocus_context4 (NoOp (ConsV v vs)) c
refocus_context4 (NoOp v1) (CPairL c e2) = refocus_expr4 (CPairR v1 c) e2
refocus_context4 (NoOp v2) (CPairR v1 c) = refocus_context4 (NoOp (PairV v1 v2)) c
refocus_context4 (NoOp v) (CUnOp uop c) = iterate4 $ VODDec (PRUnOp uop v) c
refocus_context4 (NoOp v1) (CBinOpL c bop e2) = refocus_expr4 (CBinOpR v1 bop c) e2
refocus_context4 (NoOp v2) (CBinOpR v1 bop c) = iterate4 $ VODDec (PRBinOp v1 bop v2) c

iterate4 :: ValueOrDecomposition -> Result
iterate4 (VODValue _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRBeta _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRLet _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRHandleReturn _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRHandleOp _ _ _ _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRIf _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRError _) _) = Wrong "DEAD CLAUSE"
-- Cases for BinOp left out
iterate4 (VODDec (PRUnOp Fst (PairV v1 _)) c) = refocus_context4 (NoOp v1) c
iterate4 (VODDec (PRUnOp Snd (PairV _ v2)) c) = refocus_context4 (NoOp v2) c
iterate4 (VODDec (PRUnOp uop _) _) = Wrong ("Cannot match types for un-op: " <> show uop)
iterate4 (VODDec (PRBinOp l1 Concat l2) c) = maybe
  (Wrong ("Cannot match types for bin-op: " <> show Concat)) (flip refocus_context4 c . NoOp)
  (concatListVs l1 l2)
iterate4 (VODDec (PRBinOp (IntV n1) Add (IntV n2)) c) = refocus_context4 (NoOp (IntV (n1 + n2))) c
iterate4 (VODDec (PRBinOp (IntV n1) Mul (IntV n2)) c) = refocus_context4 (NoOp (IntV (n1 * n2))) c
iterate4 (VODDec (PRBinOp _ bop _) _) = Wrong ("Cannot match types for bin-op: " <> show bop)

normalise4 :: Expr -> Result
normalise4 = refocus_expr4 CEmpty


eval5 :: Context -> Expr -> Result
eval5 _ (Var s) = Wrong ("Free variable: " <> s)
eval5 c (App ef ea) = eval5 (CAppL c ea) ef
eval5 c (Let x ev eb) = eval5 (CLet x c eb) ev
eval5 c (OpCall op e) = eval5 (COp op c) e
eval5 c (Handle h eb) = eval5 (CHandle h c) eb
eval5 c (If ec et ee) = eval5 (CIf c et ee) ec
eval5 c (Lit v) = continue5 (NoOp v) c
eval5 c (Closed v) = continue5 (NoOp v) c
-- Cases for List, Pair, and BinOp left out
eval5 c (Cons e es) = eval5 (CConsL c es) e
eval5 c (Pair e1 e2) = eval5 (CPairL c e2) e1
eval5 c (UnOp uop e) = eval5 (CUnOp uop c) e
eval5 c (BinOp e1 bop e2) = eval5 (CBinOpL c bop e2) e1

continue5 :: ValueOrOp -> Context -> Result
continue5 (NoOp v) CEmpty = Result v
continue5 (Op op v _) CEmpty =
  Wrong ("Cannot handle free op: " <> op <> "(" <> show v <> ")")
continue5 (Op op v x_op) c@(CHandle h@(Handler ops _) c') =
  case find (\(OpI op' _ _ _) -> op == op') ops of
    Just (OpI _ x k e) ->
      eval5 c' (subst x v
               (subst k (LambdaV "y" (Handle h (x_op (Var "y"))))
                e))
    Nothing ->
      let (_, f) = recompose_ss c
      in continue5 (Op op v (f . x_op)) c'
continue5 (Op op v x_op) c =
  let (c', f) = recompose_ss c
  in continue5 (Op op v (f . x_op)) c'
continue5 (NoOp v) (CAppL c e2) = eval5 (CAppR v c) e2
continue5 (NoOp v) (CAppR (LambdaV x e) c) = eval5 c (subst x v e)
continue5 (NoOp _) (CAppR v1 _) =
  Wrong ("Cannot apply non-function value: " <> show v1)
continue5 (NoOp v) (CLet x c eb) = eval5 c (subst x v eb)
continue5 (NoOp (BoolV b)) (CIf c et ee) = eval5 c (if b then et else ee)
continue5 (NoOp v) (CIf _ _ _) = Wrong ("If condition is not a boolean: " <> show v)
continue5 (NoOp v) (COp op c) = continue5 (Op op v id) c
continue5 (NoOp v) (CHandle (Handler _ (ReturnI x e)) c) = eval5 c (subst x v e)
-- Cases for List, Pair, and BinOp contexts left out
continue5 (NoOp v) (CConsL c es) = eval5 (CConsR v c) es
continue5 (NoOp vs) (CConsR v c) = continue5 (NoOp (ConsV v vs)) c
continue5 (NoOp v1) (CPairL c e2) = eval5 (CPairR v1 c) e2
continue5 (NoOp v2) (CPairR v1 c) = continue5 (NoOp (PairV v1 v2)) c
continue5 (NoOp v) (CUnOp uop c) = applyUnOp5 uop v c
continue5 (NoOp v1) (CBinOpL c bop e2) = eval5 (CBinOpR v1 bop c) e2
continue5 (NoOp v2) (CBinOpR v1 bop c) = applyBinOp5 v1 bop v2 c

--opcontinue5 :: ValueOrOp -> Context -> Result
--opcontinue5 (NoOp v) CEmpty = Result v
--opcontinue5 (NoOp v) (CAppL c e2) = eval5 (CAppR v c) e2
--opcontinue5 (NoOp v) (CAppR (LambdaV x e) c) = eval5 c (subst x v e)
--opcontinue5 (NoOp _) (CAppR v1 _) =
--  Wrong ("Cannot apply non-function value: " <> show v1)
--opcontinue5 (NoOp v) (CLet x c eb) = eval5 c (subst x v eb)
--opcontinue5 (NoOp v) (COp op c) = oppify5 op v id c
--opcontinue5 (NoOp v) (CHandle (Handler _ (ReturnI x e)) c) = eval5 c (subst x v e)
--opcontinue5 (Op op v _) CEmpty = Wrong ("Cannot handle free op: " <> op <> "(" <> show v <> ")")
--opcontinue5 (Op op v x_op) (CAppL c e2) = oppify5 op v ((\t -> App t e2) . x_op) c
--opcontinue5 (Op op v x_op) (CAppR v1 c) = oppify5 op v ((\t -> App (Closed v1) t) . x_op) c
--opcontinue5 (Op op v x_op) (CLet x c eb) = oppify5 op v ((\t -> Let x t eb) . x_op) c
--opcontinue5 (Op op v x_op) (COp op' c) = oppify5 op v ((\t -> OpCall op' t) . x_op) c
--opcontinue5 (Op op v x_op) (CHandle h@(Handler ops _) c) =
--  case find (\(OpI op' _ _) -> op == op') ops of
--    Just (OpI _ x e) -> eval5 c (subst x v
--                          (substResume (LambdaV "y" (Handle h (x_op (Var "y")))) e))
--    Nothing -> oppify5 op v ((\t -> Handle h t) . x_op) c
---- Cases for List, Pair, and BinOp contexts left out
--opcontinue5 (NoOp v) (CList vs c []) = continue5 (ListV (vs <> [v])) c
--opcontinue5 (NoOp v) (CList vs c (e : es)) = eval5 (CList (vs <> [v]) c es) e
--opcontinue5 (NoOp v1) (CPairL c e2) = eval5 (CPairR v1 c) e2
--opcontinue5 (NoOp v2) (CPairR v1 c) = continue5 (PairV v1 v2) c
--opcontinue5 (NoOp v1) (CBinOpL c bop e2) = eval5 (CBinOpR v1 bop c) e2
--opcontinue5 (NoOp v2) (CBinOpR v1 bop c) = applyBinOp5 v1 bop v2 c
--opcontinue5 (Op op v x_op) (CList vs c es) = oppify5 op v ((\t -> List ((Closed <$> vs) <> (t : es))) . x_op) c
--opcontinue5 (Op op v x_op) (CPairL c e2) = oppify5 op v ((\t -> Pair t e2) . x_op) c
--opcontinue5 (Op op v x_op) (CPairR v1 c) = oppify5 op v ((\t -> Pair (Closed v1) t) . x_op) c
--opcontinue5 (Op op v x_op) (CBinOpL c bop e2) = oppify5 op v ((\t -> BinOp t bop e2) . x_op) c
--opcontinue5 (Op op v x_op) (CBinOpR v1 bop c) = oppify5 op v ((\t -> BinOp (Closed v1) bop t) . x_op) c


applyUnOp5 :: UnOpOperator -> Value -> Context -> Result
applyUnOp5 Fst (PairV v1 _) c = continue5 (NoOp v1) c
applyUnOp5 Snd (PairV _ v2) c = continue5 (NoOp v2) c
applyUnOp5 uop _ _ = Wrong ("Cannot match types for un-op: " <> show uop)

applyBinOp5 :: Value -> BinOpOperator -> Value -> Context -> Result
applyBinOp5 l1 Concat l2 c = maybe
  (Wrong ("Cannot match types for bin-op: " <> show Concat)) (flip continue5 c . NoOp)
  (concatListVs l1 l2)
applyBinOp5 (IntV n1) Add (IntV n2) c = continue5 (NoOp (IntV (n1 + n2))) c
applyBinOp5 (IntV n1) Mul (IntV n2) c = continue5 (NoOp (IntV (n1 * n2))) c
applyBinOp5 _ bop _ _ = Wrong ("Cannot match types for bin-op: " <> show bop)

normalise5 :: Expr -> Result
normalise5 = eval5 CEmpty



--eval5 c (App ef ea)  /  eval6 (App ef ea) kv ko
eval5_vf (App ef ea) c = eval5 (CAppL c ea) ef
-- > fill in the clause for: continue5 vf (CAppL CEmpty ea)
eval5_v2 :: Expr -> p -> (String -> Value -> (Expr -> Expr) -> Result) -> Result
eval5_v2 (App ef ea) kv ko = eval6 ea (\vf -> eval5 (CAppR vf CEmpty) ea)
               (\op v x_op -> ko op v ((\t -> App t ea) . x_op))
-- > fill in the clause for: continue5 va (CAppR vf CEmpty)
eval5_v3 :: Expr -> p -> (String -> Value -> (Expr -> Expr) -> Result) -> Result
eval5_v3 (App ef ea) kv ko = eval6 ef (\vf ->
        eval6 ea (\va -> case vf of
                      LambdaV x e -> eval5 CEmpty (subst x va e)
                      _ -> Wrong ("Cannot apply non-function value: " <> show vf))
                 (\op v x_op -> ko op v ((\t -> App (Closed vf) t) . x_op)))
               (\op v x_op -> ko op v ((\t -> App t ea) . x_op))
-- > fill in the clause for: eval5 CEmpty e
eval5_v4 :: Expr -> (Value -> Result) -> (String -> Value -> (Expr -> Expr) -> Result) -> Result
eval5_v4 (App ef ea) kv ko = eval6 ef (\vf ->
        eval6 ea (\va -> case vf of
                      LambdaV x e -> eval6 (subst x va e) kv ko
                      _ -> Wrong ("Cannot apply non-function value: " <> show vf))
                 (\op v x_op -> ko op v ((\t -> App (Closed vf) t) . x_op)))
               (\op v x_op -> ko op v ((\t -> App t ea) . x_op))


-- ^ look up isomorphism in paper Defunctionalized evalers... from Danvy

eval6
  :: Expr
  -> (Value -> Result)
  -> (String -> Value -> (Expr -> Expr) -> Result)
  -> Result
eval6 (Var s) _ _ = Wrong ("Free variable: " <> s)
eval6 (App ef ea) kv ko =
  eval6 ef (\vf ->
    eval6 ea (\va -> case vf of
      LambdaV x e -> eval6 (subst x va e) kv ko
      _ -> Wrong ("Cannot apply non-function value: " <> show vf))
      (\op v x_op -> ko op v ((\t -> App (Closed vf) t) . x_op)))
    (\op v x_op -> ko op v ((\t -> App t ea) . x_op))
eval6 (Let x ev eb) kv ko =
  eval6 ev (\v ->
    eval6 (subst x v eb) kv ko)
    (\op v x_op -> ko op v ((\t -> Let x t eb) . x_op))
eval6 (OpCall op e) _ ko =
  eval6 e (\v -> ko op v id)
    (\op' v x_op -> ko op' v ((\t -> OpCall op t) . x_op))
eval6 (Handle h@(Handler ops (ReturnI xr er)) eb) kv ko =
  eval6 eb
    (\bv -> eval6 (subst xr bv er) kv ko)
    (\op v x_op ->
      case find (\(OpI op' _ _ _) -> op == op') ops of
        Just (OpI _ x k e) ->
          eval6 (subst x v
                (subst k (LambdaV "y" (Handle h (x_op (Var "y"))))
                 e))
                kv ko
        Nothing -> ko op v ((\t -> Handle h t) . x_op))
eval6 (If ec et ee) kv ko =
  eval6 ec
    (\case
        BoolV b -> eval6 (if b then et else ee) kv ko
        v -> Wrong ("If condition is not a boolean: " <> show v))
    (\op v x_op -> ko op v ((\t -> If t et ee) . x_op))
eval6 (Lit v) kv _ = kv v
eval6 (Closed v) kv _ = kv v
-- Cases for List, Pair, and BinOp left out
eval6 (Cons e es) kv ko =
  eval6 e (\vh ->
    eval6 es (\vs -> kv (ConsV vh vs))
      (\op v x_op -> ko op v ((\t -> Cons (Closed vh) t) . x_op)))
    (\op v x_op -> ko op v ((\t -> Cons t es) . x_op))
eval6 (Pair e1 e2) kv ko =
  eval6 e1 (\v1 ->
    eval6 e2 (\v2 -> kv (PairV v1 v2))
      (\op v x_op -> ko op v ((\t -> Pair (Closed v1) t) . x_op)))
    (\op v x_op -> ko op v ((\t -> Pair t e2) . x_op))
eval6 (UnOp uop e) kv ko =
  eval6 e (\v ->
    applyUnOp6 uop v kv)
    (\op v x_op -> ko op v ((\t -> UnOp uop t) . x_op))
eval6 (BinOp e1 bop e2) kv ko =
  eval6 e1 (\v1 ->
    eval6 e2 (\v2 -> applyBinOp6 v1 bop v2 kv)
      (\op v x_op -> ko op v ((\t -> BinOp (Closed v1) bop t) . x_op)))
    (\op v x_op -> ko op v ((\t -> BinOp t bop e2) . x_op))

applyUnOp6 :: UnOpOperator -> Value -> (Value -> Result) -> Result
applyUnOp6 Fst (PairV v1 _) kv = kv v1
applyUnOp6 Snd (PairV _ v2) kv = kv v2
applyUnOp6 uop _ _ = Wrong ("Cannot match types for un-op: " <> show uop)

applyBinOp6 :: Value -> BinOpOperator -> Value -> (Value -> Result) -> Result
applyBinOp6 l1 Concat l2 kv = maybe
  (Wrong ("Cannot match types for bin-op: " <> show Concat)) kv
  (concatListVs l1 l2)
applyBinOp6 (IntV n1) Add (IntV n2) kv = kv (IntV (n1 + n2))
applyBinOp6 (IntV n1) Mul (IntV n2) kv = kv (IntV (n1 * n2))
applyBinOp6 _ bop _ _ = Wrong ("Cannot match types for bin-op: " <> show bop)

normalise6 :: Expr -> Result
normalise6 e = eval6 e Result (\op v _ -> Wrong ("Cannot handle free op: " <> op <> "(" <> show v <> ")"))




--construct_oppify6 :: (Expr -> Expr) -> (ValueOrOp -> Result) -> (ValueOrOp -> Result)
--construct_oppify6 _ k (NoOp v) = k (NoOp v)
--construct_oppify6 x_op' k (Op op v x_op) = k (Op op v (x_op' . x_op))
--
--eval_list6
--  :: [Expr]
--  -> (ValueOrOp -> Result)
--  -> [Value] -> Result
--eval_list6 [] k vs = k (NoOp (ListV vs))
--eval_list6 (e : es) k vs = eval6 e (\case
--  NoOp v -> eval_list6 es k (vs <> [v])
--  op -> construct_oppify6 (\t -> List ((Closed <$> vs) <> (t : es))) k op)
--
--eval6
--  :: Expr
--  -> (ValueOrOp -> Result)
--  -> Result
--eval6 (Var s) _ = Wrong ("Free variable: " <> s)
--eval6 (App ef ea) k =
--  eval6 e1 (\case
--    NoOp v1 -> eval6 e2 (\case
--      NoOp v2 -> case v1 of
--        LambdaV x e -> eval6 (subst x v2 e) k
--        _ -> Wrong ("Cannot apply non-function value: " <> show v1)
--      op -> construct_oppify6 (\t -> App (Closed v1) t) k op)
--    op -> construct_oppify6 (\t -> App t e2) k op)
--eval6 (Let x ev eb) k =
--  eval6 ev (\case
--    NoOp v -> eval6 (subst x v eb) k
--    op -> construct_oppify6 (\t -> Let x t eb) k op)
--eval6 (OpCall op e) k =
--  eval6 e (\case
--    NoOp v -> k (Op op v id)
--    op' -> construct_oppify6 (\t -> OpCall op t) k op')
--eval6 (Handle h@(Handler ops (ReturnI xr er)) eb) k =
--  eval6 eb (\case
--    NoOp bv -> eval6 (subst xr bv er) k
--    Op op v x_op ->
--      case find (\(OpI op' _ _) -> op == op') ops of
--        Just (OpI _ x e) ->
--          eval6 (subst x v
--            (substResume (LambdaV "y" (Handle h (x_op (Var "y")))) e))
--            k
--        Nothing -> k (Op op v ((\t -> Handle h t) . x_op)))
--eval6 (Lit v) k = k (NoOp v)
--eval6 (Closed v) k = k (NoOp v)
---- Cases for List, Pair, and BinOp left out
--eval6 (List es) k = eval_list6 es k []
--eval6 (Pair e1 e2) k =
--  eval6 e1 (\case
--    NoOp v1 -> eval6 e2 (\case
--      NoOp v2 -> k (NoOp (PairV v1 v2))
--      op -> construct_oppify6 (\t -> Pair (Closed v1) t) k op)
--    op -> construct_oppify6 (\t -> Pair t e2) k op)
--eval6 (BinOp e1 bop e2) k =
--  eval6 e1 (\case
--    NoOp v1 -> eval6 e2 (\case
--      NoOp v2 -> apply6 v1 bop v2 (k . NoOp)
--      op -> construct_oppify6 (\t -> BinOp (Closed v1) bop t) k op)
--    op -> construct_oppify6 (\t -> BinOp t bop e2) k op)
--
--apply6 :: Value -> BinOpOperator -> Value -> (Value -> Result) -> Result
--apply6 (ListV l1) Concat (ListV l2) k = k (ListV (l1 <> l2))
--apply6 (IntV n1) Add (IntV n2) k = k (IntV (n1 + n2))
--apply6 (IntV n1) Mul (IntV n2) k = k (IntV (n1 * n2))
--apply6 _ bop _ _ = Wrong ("Cannot match types for bin-op: " <> show bop)



data Result7
  = NoOp7 Value
  | Op7 String Value (Expr -> Expr)
  | Wrong7 String
  deriving (Show)

check_result7 :: Result7
              -> (Value -> Result7)
              -> (Expr -> Expr)
              -> Result7
check_result7 (NoOp7 v) kv _ = kv v
check_result7 (Op7 op v x_op) _ x_op' = Op7 op v (x_op' . x_op)
check_result7 (Wrong7 err) _ _ = Wrong7 err

eval7' :: Expr -> Result7
eval7' (App ef ea) =
  case (eval7' ef) of
    NoOp7 vf -> case eval7' ea of
      NoOp7 va -> case vf of
        LambdaV x e -> eval7' (subst x va e)
        _ -> Wrong7 ("Cannot apply non-function value: " <> show vf)
      Op7 op v x_op -> Op7 op v ((\t -> App (Closed vf) t) . x_op)
      Wrong7 err -> Wrong7 err
    Op7 op v x_op -> Op7 op v ((\t -> App t ea) . x_op)
    Wrong7 err -> Wrong7 err

eval7
  :: Expr
  -> Result7
eval7 (Var s) = Wrong7 ("Free variable: " <> s)
eval7 (App ef ea) =
  check_result7 (eval7 ef)
    (\vf -> check_result7 (eval7 ea)
      (\va -> case vf of
        LambdaV x e -> eval7 (subst x va e)
        _ -> Wrong7 ("Cannot apply non-function value: " <> show vf))
      (\t -> App (Closed vf) t))
    (\t -> App t ea)
eval7 (Let x ev eb) =
  check_result7 (eval7 ev)
    (\v -> eval7 (subst x v eb))
    (\t -> Let x t eb)
eval7 (OpCall op e) =
  check_result7 (eval7 e)
    (\v -> Op7 op v id)
    (\t -> OpCall op t)
eval7 (Handle h@(Handler ops (ReturnI xr er)) eb) =
  case eval7 eb of
    NoOp7 bv -> eval7 (subst xr bv er)
    Op7 op v x_op ->
      case find (\(OpI op' _ _ _) -> op == op') ops of
        Just (OpI _ x k e) ->
          eval7 (subst x v
            (subst k (LambdaV "y" (Handle h (x_op (Var "y")))) e))
        Nothing -> Op7 op v ((\t -> Handle h t) . x_op)
    Wrong7 err -> Wrong7 err
eval7 (If ec et ee) =
  check_result7 (eval7 ec)
    (\case
        BoolV b -> eval7 (if b then et else ee)
        v -> Wrong7 ("If condition is not a boolean: " <> show v))
    (\t -> If t et ee)
eval7 (Lit v) = NoOp7 v
eval7 (Closed v) = NoOp7 v
-- Cases for List, Pair, and BinOp left out
eval7 (Cons e es) =
  check_result7 (eval7 e)
    (\vh -> check_result7 (eval7 es)
      (\vs -> NoOp7 (ConsV vh vs))
      (\t -> Cons (Closed vh) t))
    (\t -> Cons t es)
eval7 (Pair e1 e2) =
  check_result7 (eval7 e1)
    (\v1 -> check_result7 (eval7 e2)
      (\v2 -> NoOp7 (PairV v1 v2))
      (\t -> Pair (Closed v1) t))
    (\t -> Pair t e2)
eval7 (UnOp uop e) =
  check_result7 (eval7 e)
    (\v -> applyUnOp7 uop v)
    (\t -> UnOp uop t)
eval7 (BinOp e1 bop e2) =
  check_result7 (eval7 e1)
    (\v1 -> check_result7 (eval7 e2)
      (\v2 -> applyBinOp7 v1 bop v2)
      (\t -> BinOp (Closed v1) bop t))
    (\t -> BinOp t bop e2)

applyUnOp7 :: UnOpOperator -> Value -> Result7
applyUnOp7 Fst (PairV v1 _) = NoOp7 v1
applyUnOp7 Snd (PairV _ v2) = NoOp7 v2
applyUnOp7 uop _ = Wrong7 ("Cannot match types for un-op: " <> show uop)

applyBinOp7 :: Value -> BinOpOperator -> Value -> Result7
applyBinOp7 l1 Concat l2 = maybe
  (Wrong7 ("Cannot match types for bin-op: " <> show Concat)) NoOp7
  (concatListVs l1 l2)
applyBinOp7 (IntV n1) Add (IntV n2) = NoOp7 (IntV (n1 + n2))
applyBinOp7 (IntV n1) Mul (IntV n2) = NoOp7 (IntV (n1 * n2))
applyBinOp7 _ bop _ = Wrong7 ("Cannot match types for bin-op: " <> show bop)



-- 3. Embed named and unnamed functions with (Value -> Expr) functions instead of variables.

-- Values, including value types needed to demonstrate evaler capabilities
data Value8
  = LambdaV8 (Value8 -> Expr8)
  | IntV8 Int
  | BoolV8 Bool

  | UnitV8
  | PairV8 Value8 Value8
  | NilV8
  | ConsV8 Value8 Value8
  deriving (Show)

data OpI8 = OpI8 String (Value8 -> (Value8 -> Expr8) -> Expr8)
  deriving (Show)
data Handler8 = Handler8 [OpI8] (Value8 -> Expr8)
  deriving (Show)

-- Higher order AST something HOAS!!

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr8
  = App8 Expr8 Expr8
  | Let8 Expr8 (Value8 -> Expr8)
  | OpCall8 String Expr8
  | Handle8 Handler8 Expr8
  | Lit8 Value8

  | If8 Expr8 Expr8 Expr8
  | Pair8 Expr8 Expr8
  | Nil8
  | Cons8 Expr8 Expr8
  | UnOp8 UnOpOperator Expr8
  | BinOp8 Expr8 BinOpOperator Expr8
  deriving (Show)

data Result8
  = NoOp8 Value8
  | Op8 String Value8 (Value8 -> Expr8)
  deriving (Show)

check_result8 :: Result8 -> (Value8 -> Result8) -> (Expr8 -> Expr8) -> Result8
check_result8 (NoOp8 v) kv _ = kv v
check_result8 (Op8 op v x_op) _ x_op' = Op8 op v (x_op' . x_op)

eval8
  :: Expr8
  -> Result8
eval8 (App8 ef ea) =
  check_result8 (eval8 ef)
    (\vf -> check_result8 (eval8 ea)
      (\va -> case vf of
        LambdaV8 body -> eval8 (body va)
        _ -> error ("Cannot apply non-function value: " <> show vf))
      (\t -> App8 (Lit8 vf) t))
    (\t -> App8 t ea)
eval8 (Let8 ev body) =
  check_result8 (eval8 ev)
    (\v -> eval8 (body v))
    (\t -> Let8 t body)
eval8 (OpCall8 op e) =
  check_result8 (eval8 e)
    (\v -> Op8 op v Lit8)
    (\t -> OpCall8 op t)
eval8 (Handle8 h@(Handler8 ops ret) eb) =
  case eval8 eb of
    NoOp8 bv -> eval8 (ret bv)
    Op8 op v x_op ->
      case find (\(OpI8 op' _) -> op == op') ops of
        Just (OpI8 _ body) ->
          eval8 (body v (\y -> (Handle8 h (x_op y))))
        Nothing -> Op8 op v ((\t -> Handle8 h t) . x_op)
eval8 (If8 ec et ee) =
  check_result8 (eval8 ec)
    (\case
        BoolV8 b -> eval8 (if b then et else ee)
        v -> error ("If condition is not a boolean: " <> show v))
    (\t -> If8 t et ee)
eval8 (Lit8 v) = NoOp8 v
-- Cases for List, Pair, and BinOp left out
eval8 Nil8 = NoOp8 NilV8
eval8 (Cons8 e es) =
  check_result8 (eval8 e)
    (\vh -> check_result8 (eval8 es)
      (\vs -> NoOp8 (ConsV8 vh vs))
      (\t -> Cons8 (Lit8 vh) t))
    (\t -> Cons8 t es)
eval8 (Pair8 e1 e2) =
  check_result8 (eval8 e1)
    (\v1 -> check_result8 (eval8 e2)
      (\v2 -> NoOp8 (PairV8 v1 v2))
      (\t -> Pair8 (Lit8 v1) t))
    (\t -> Pair8 t e2)
eval8 (UnOp8 uop e) =
  check_result8 (eval8 e)
    (\v -> applyUnOp8 uop v)
    (\t -> UnOp8 uop t)
eval8 (BinOp8 e1 bop e2) =
  check_result8 (eval8 e1)
    (\v1 -> check_result8 (eval8 e2)
      (\v2 -> applyBinOp8 v1 bop v2)
      (\t -> BinOp8 (Lit8 v1) bop t))
    (\t -> BinOp8 t bop e2)

applyUnOp8 :: UnOpOperator -> Value8 -> Result8
applyUnOp8 Fst (PairV8 v1 _) = NoOp8 v1
applyUnOp8 Snd (PairV8 _ v2) = NoOp8 v2
applyUnOp8 uop _ = error ("Cannot match types for un-op: " <> show uop)

applyBinOp8 :: Value8 -> BinOpOperator -> Value8 -> Result8
applyBinOp8 l1 Concat l2 = maybe
  (error ("Cannot match types for bin-op: " <> show Concat)) NoOp8
  (concatListVs8 l1 l2)
applyBinOp8 (IntV8 n1) Add (IntV8 n2) = NoOp8 (IntV8 (n1 + n2))
applyBinOp8 (IntV8 n1) Mul (IntV8 n2) = NoOp8 (IntV8 (n1 * n2))
applyBinOp8 _ bop _ = error ("Cannot match types for bin-op: " <> show bop)

concatListVs8 :: Value8 -> Value8 -> Maybe Value8
concatListVs8 NilV8 NilV8 = Just NilV8
concatListVs8 NilV8 vs' = Just vs'
concatListVs8 vs NilV8 = Just vs
concatListVs8 (ConsV8 v vs) vs' = ConsV8 v <$> (concatListVs8 vs vs')
concatListVs8 _ _ = Nothing

-- 4. Remove all non-essential language features (application) through Lets
-- Values, including value types needed to demonstrate evaler capabilities
data Value9
  = LambdaV9 (Value9 -> Expr9)
  | IntV9 Int
  | BoolV9 Bool

  | UnitV9
  | PairV9 Value9 Value9
  | NilV9
  | ConsV9 Value9 Value9
  deriving (Show)

data OpI9 = OpI9 String (Value9 -> (Value9 -> Expr9) -> Expr9)
  deriving (Show)
data Handler9 = Handler9 [OpI9] (Value9 -> Expr9)
  deriving (Show)

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr9
  = Let9 Expr9 (Value9 -> Expr9)
  | OpCall9 String Value9
  | Handle9 Handler9 Expr9
  | Lit9 Value9
  deriving (Show)

data Result9
  = NoOp9 Value9
  | Op9 String Value9 (Value9 -> Expr9)
  deriving (Show)

check_result9 :: Result9 -> (Value9 -> Result9) -> (Expr9 -> Expr9) -> Result9
check_result9 (NoOp9 v) kv _ = kv v
check_result9 (Op9 op v x_op) _ x_op' = Op9 op v (x_op' . x_op)

app8 :: Expr8 -> Expr8 -> Expr8
app8 ef ea =
  Let8 ef (\vf ->
    Let8 ea (\va -> case vf of
      LambdaV8 body -> body va
      _ -> error ("Cannot apply non-function value: " <> show vf)))

app9 :: Expr9 -> Expr9 -> Expr9
app9 ef ea =
  Let9 ef (\vf ->
    Let9 ea (\va -> case vf of
      LambdaV9 body -> body va
      _ -> error ("Cannot apply non-function value: " <> show vf)))

-- Showing that these definitions are equivalent
--eval8 (App8 ef ea) = eval8 (app8 e1 e2)
--eval8 (Let8 ev body) =
--  check_result8 (eval8 ev)
--    (\v -> eval8 (body v))
--    (\t -> Let8 t body)
-- Show that eval8 (app8 e1 e2) is the same as eval8 (App8 ef ea),
-- making app8 e1 e2 encode the same program under eval8 as App8 ef ea
eval8_v1 :: Expr8 -> Result8
eval8_v1 (App8 ef ea) = eval8 (app8 ef ea)
eval8_v2 :: Expr8 -> Result8
eval8_v2 (App8 ef ea) = eval8 (
  Let8 ef (\vf ->
    Let8 ea (\va -> case vf of
      LambdaV8 body -> body va
      _ -> error ("Cannot apply non-function value: " <> show vf))))
eval8_v3 :: Expr8 -> Result8
eval8_v3 (App8 ef ea) = check_result8 (eval8 ef)
   (\vf ->
      eval8 (Let8 ea (\va -> case vf of
        LambdaV8 body -> body va
        _ -> error ("Cannot apply non-function value: " <> show vf))))
   (\t ->
     Let8 t (\vf ->
       Let8 ea (\va -> case vf of
         LambdaV8 body -> body va
         _ -> error ("Cannot apply non-function value: " <> show vf))))
eval8_v4 :: Expr8 -> Result8
eval8_v4 (App8 ef ea) = check_result8 (eval8 ef)
   (\vf ->
      eval8 (Let8 ea (\va -> case vf of
        LambdaV8 body -> body va
        _ -> error ("Cannot apply non-function value: " <> show vf))))
   (\t -> app8 t ea)
eval8_v5 :: Expr8 -> Result8
eval8_v5 (App8 ef ea) = check_result8 (eval8 ef)
   (\vf ->
      check_result8 (eval8 ea)
        (\va -> eval8 (case vf of
            LambdaV8 body -> body va
            _ -> error ("Cannot apply non-function value: " <> show vf)))
        (\t -> Let8 t (\va ->
                  case vf of
                    LambdaV8 body -> body va
                    _ -> error ("Cannot apply non-function value: " <> show vf))))
   (\t -> app8 t ea)
eval8_v6 :: Expr8 -> Result8
eval8_v6 (App8 ef ea) = check_result8 (eval8 ef)
   (\vf ->
      check_result8 (eval8 ea)
        (\va -> case vf of
            LambdaV8 body -> eval8 (body va)
            _ -> error ("Cannot apply non-function value: " <> show vf))
        (\t -> Let8 (Lit8 vf) (\vf -> Let8 t (\va ->
                  case vf of
                    LambdaV8 body -> body va
                    _ -> error ("Cannot apply non-function value: " <> show vf)))))
   (\t -> app8 t ea)
eval8_v7 :: Expr8 -> Result8
eval8_v7 (App8 ef ea) = check_result8 (eval8 ef)
   (\vf ->
      check_result8 (eval8 ea)
        (\va -> case vf of
            LambdaV8 body -> eval8 (body va)
            _ -> error ("Cannot apply non-function value: " <> show vf))
        (\t -> app8 (Lit8 vf) t))
   (\t -> app8 t ea)

-- Those for list, pair, binops

list9 :: [Expr9] -> Expr9
list9 [] = Lit9 NilV9
list9 (e : es) =
  Let9 e (\v ->
    Let9 (list9 es) (\vs ->
      Lit9 (ConsV9 v vs)))

cons9 :: Expr9 -> Expr9 -> Expr9
cons9 e es = Let9 e (\v -> Let9 es (\vs -> Lit9 (ConsV9 v vs)))

pair9 :: Expr9 -> Expr9 -> Expr9
pair9 e1 e2 =
  Let9 e1 (\v1 ->
    Let9 e2 (\v2 ->
      Lit9 (PairV9 v1 v2)))

if9 :: Expr9 -> Expr9 -> Expr9 -> Expr9
if9 ec et ee =
  Let9 ec (\case
    BoolV9 b -> if b then et else ee
    v -> error ("If condition is not a boolean: " <> show v))

unOp9 :: UnOpOperator -> Expr9 -> Expr9
unOp9 uop e =
  Let9 e (\v ->
    Lit9 (applyUnOp9 uop v))

binOp9 :: Expr9 -> BinOpOperator -> Expr9 -> Expr9
binOp9 e1 bop e2 =
  Let9 e1 (\v1 ->
    Let9 e2 (\v2 ->
      Lit9 (applyBinOp9 v1 bop v2)))

op9 :: String -> Expr9 -> Expr9
op9 op e = Let9 e (\v -> OpCall9 op v)


eval9 :: Expr9 -> Result9
eval9 (Let9 ev body) =
  check_result9 (eval9 ev)
    (\v -> eval9 (body v))
    (\t -> Let9 t body)
eval9 (OpCall9 op v) = Op9 op v Lit9
eval9 (Handle9 h@(Handler9 ops ret) eb) =
  case eval9 eb of
    NoOp9 bv -> eval9 (ret bv)
    Op9 op v x_op ->
      case find (\(OpI9 op' _) -> op == op') ops of
        Just (OpI9 _ body) ->
          eval9 (body v (\y -> (Handle9 h (x_op y))))
        Nothing -> Op9 op v ((\t -> Handle9 h t) . x_op)
eval9 (Lit9 v) = NoOp9 v

applyUnOp9 :: UnOpOperator -> Value9 -> Value9
applyUnOp9 Fst (PairV9 v1 _) = v1
applyUnOp9 Snd (PairV9 _ v2) = v2
applyUnOp9 uop _ = error ("Cannot match types for un-op: " <> show uop)

applyBinOp9 :: Value9 -> BinOpOperator -> Value9 -> Value9
applyBinOp9 l1 Concat l2 = maybe
  (error ("Cannot match types for bin-op: " <> show Concat)) id
  (concatListVs9 l1 l2)
applyBinOp9 (IntV9 n1) Add (IntV9 n2) = IntV9 (n1 + n2)
applyBinOp9 (IntV9 n1) Mul (IntV9 n2) = IntV9 (n1 * n2)
applyBinOp9 _ bop _ = error ("Cannot match types for bin-op: " <> show bop)

concatListVs9 :: Value9 -> Value9 -> Maybe Value9
concatListVs9 NilV9 NilV9 = Just NilV9
concatListVs9 NilV9 vs' = Just vs'
concatListVs9 vs NilV9 = Just vs
concatListVs9 (ConsV9 v vs) vs' = ConsV9 v <$> (concatListVs9 vs vs')
concatListVs9 _ _ = Nothing


-- 5. Encode operations as data using intrinsic typing rules for Values etc.

-- Values, including value types needed to demonstrate evaler capabilities
data Value10 a where
  LambdaV10 :: (Value10 x -> Expr10 sig a) -> Value10 (x -> Expr10 sig a)
  IntV10 :: Int -> Value10 Int
  BoolV10 :: Bool -> Value10 Bool
  UnitV10 :: Value10 ()
  PairV10 :: Value10 x -> Value10 y -> Value10 (x, y)
  NilV10 :: Value10 [x]
  ConsV10 :: Value10 x -> Value10 [x] -> Value10 [x]

data Handler10 eff r a w where
  Handler10  ::  (forall x. eff x
                 -> (Value10 x -> Expr10 r w) 
                 -> Expr10 r w)
             ->  (Value10 a -> Expr10 r w)
             ->  Handler10 eff r a w

-- Unary operators, but typed
data UnOpOperator10 x a where
  Fst10 :: UnOpOperator10 (x, y) x
  Snd10 :: UnOpOperator10 (x, y) y

-- Binary operators, but typed
data BinOpOperator10 x y a where
  Add10 :: BinOpOperator10 Int Int Int
  Mul10 :: BinOpOperator10 Int Int Int
  Concat10 :: BinOpOperator10 [a] [a] [a]

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr10 sig a where
  Let10 :: Expr10 sig x -> (Value10 x -> Expr10 sig a) -> Expr10 sig a
  OpCall10 :: sig a -> Expr10 sig a
  Handle10  ::  Handler10 eff r a w 
            ->  Expr10 (eff :++: r) a
            ->  Expr10 r w
  Lit10 :: Value10 a -> Expr10 sig a

data Result10 sig a where
  NoOp10 :: Value10 a -> Result10 sig a
  Op10 :: sig x -> (Value10 x -> Expr10 sig a) -> Result10 sig a



app10 :: Expr10 sig (x -> Expr10 sig a) -> Expr10 sig x -> Expr10 sig a
app10 ef ea =
  Let10 ef (\vf ->
    Let10 ea (\va -> case vf of
       LambdaV10 body -> body va))

pair10 :: Expr10 sig x -> Expr10 sig y -> Expr10 sig (x, y)
pair10 e1 e2 =
  Let10 e1 (\v1 ->
    Let10 e2 (\v2 -> Lit10 (PairV10 v1 v2)))

cons10 :: Expr10 sig x -> Expr10 sig [x] -> Expr10 sig [x]
cons10 e es =
  Let10 e (\v ->
    Let10 es (\vs ->
      Lit10 (ConsV10 v vs)))

list10 :: [Expr10 sig x] -> Expr10 sig [x]
list10 [] = Lit10 NilV10
list10 (e : es) = Let10 e (\v -> Let10 (list10 es) (\vs -> Lit10 (ConsV10 v vs)))

op10 :: eff :<<: sig => (Value10 x -> eff a) -> Expr10 sig x -> Expr10 sig a
op10 op e = Let10 e (OpCall10 . inj . op)

data St10 s a where
  Get10 :: Value10 () -> St10 s s
  Put10 :: Value10 s -> St10 s ()

get10 :: St10 s :<<: sig => Expr10 sig () -> Expr10 sig s
get10 = op10 Get10

put10 :: St10 s :<<: sig => Expr10 sig s -> Expr10 sig ()
put10 = op10 Put10

unOp10 :: UnOpOperator10 x a -> Expr10 sig x -> Expr10 sig a
unOp10 uop e =
  Let10 e (\v ->
    Lit10 (applyUnOp10 uop v))

binOp10 :: Expr10 sig x -> BinOpOperator10 x y a -> Expr10 sig y -> Expr10 sig a
binOp10 e1 bop e2 =
  Let10 e1 (\v1 ->
    Let10 e2 (\v2 ->
      Lit10 (applyBinOp10 v1 bop v2)))

if10 :: Expr10 sig Bool -> Expr10 sig a -> Expr10 sig a -> Expr10 sig a
if10 ec et ee =
  Let10 ec (\case
    BoolV10 b -> if b then et else ee)

-- Show almost possible step for op here

check_result10 :: Result10 sig x -> (Value10 x -> Result10 sig a) -> (Expr10 sig x -> Expr10 sig a) -> Result10 sig a
check_result10 (NoOp10 v) k _ = k v
check_result10 (Op10 op x_op) _ x_op' = Op10 op (x_op' . x_op)

eval10 :: Expr10 sig a -> Result10 sig a
eval10 (Let10 ev body) =
  check_result10 (eval10 ev)
    (\v -> eval10 (body v))
    (\t -> Let10 t body)
eval10 (OpCall10 op) = Op10 op Lit10
eval10 (Handle10 h@(Handler10 ops ret) eb) =
  case eval10 eb of
    NoOp10 bv -> eval10 (ret bv)
    Op10 (Inl op) x_op -> eval10 (ops op (\y -> (Handle10 h (x_op y))))
    Op10 (Inr op) x_op -> Op10 op ((\t -> Handle10 h t) . x_op)
eval10 (Lit10 v) = NoOp10 v

applyUnOp10 :: UnOpOperator10 x a -> Value10 x -> Value10 a
applyUnOp10 Fst10 (PairV10 v1 _) = v1
applyUnOp10 Snd10 (PairV10 _ v2) = v2

applyBinOp10 :: Value10 x -> BinOpOperator10 x y a -> Value10 y -> Value10 a
applyBinOp10 l1 Concat10 l2 = concatListVs10 l1 l2
applyBinOp10 (IntV10 n1) Add10 (IntV10 n2) = IntV10 (n1 + n2)
applyBinOp10 (IntV10 n1) Mul10 (IntV10 n2) = IntV10 (n1 * n2)

concatListVs10 :: Value10 [x] -> Value10 [x] -> Value10 [x]
concatListVs10 NilV10 NilV10 = NilV10
concatListVs10 NilV10 vs' = vs'
concatListVs10 vs NilV10 = vs
concatListVs10 (ConsV10 v vs) vs' = ConsV10 v (concatListVs10 vs vs')


-- 6. Remove Values (we can be more general now)

-- Values, including value types needed to demonstrate evaler capabilities
data Handler11 eff r a w where
  Handler11 :: (forall x. eff x -> (x -> Expr11 r w) -> Expr11 r w)
            -> (a -> Expr11 r w)
            -> Handler11 eff r a w

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr11 sig a where
  Let11 :: Expr11 sig x -> (x -> Expr11 sig a) -> Expr11 sig a
  OpCall11 :: sig a -> Expr11 sig a
  Handle11 :: Handler11 eff r a w -> Expr11 (eff :++: r) a -> Expr11 r w
  Lit11 :: a -> Expr11 sig a

data Result11 sig a where
  NoOp11 :: a -> Result11 sig a
  Op11 :: sig x -> (x -> Expr11 sig a) -> Result11 sig a



app11 :: Expr11 sig (x -> Expr11 sig a) -> Expr11 sig x -> Expr11 sig a
app11 ef ea =
  Let11 ef (\body ->
    Let11 ea (\va -> body va))

pair11 :: Expr11 sig x -> Expr11 sig y -> Expr11 sig (x, y)
pair11 e1 e2 =
  Let11 e1 (\v1 ->
    Let11 e2 (\v2 -> Lit11 (v1, v2)))

cons11 :: Expr11 sig x -> Expr11 sig [x] -> Expr11 sig [x]
cons11 e es =
  Let11 e (\v ->
    Let11 es (\vs ->
      Lit11 (v : vs)))

list11 :: [Expr11 sig x] -> Expr11 sig [x]
list11 [] = Lit11 []
list11 (e : es) = Let11 e (\v -> Let11 (list11 es) (\vs -> Lit11 (v : vs)))

unOp11 :: (x -> a) -> Expr11 sig x -> Expr11 sig a
unOp11 uop e =
  Let11 e (\v ->
    Lit11 (uop v))

binOp11 :: Expr11 sig x -> (x -> y -> a) -> Expr11 sig y -> Expr11 sig a
binOp11 e1 bop e2 =
  Let11 e1 (\v1 ->
    Let11 e2 (\v2 ->
      Lit11 (bop v1 v2)))

if11 :: Expr11 sig Bool -> Expr11 sig a -> Expr11 sig a -> Expr11 sig a
if11 ec et ee =
  Let11 ec (\b -> if b then et else ee)

op11 :: eff :<<: sig => (x -> eff a) -> Expr11 sig x -> Expr11 sig a
op11 op e = Let11 e (OpCall11 . inj . op)

check_result11 :: Result11 sig x -> (x -> Result11 sig a) -> (Expr11 sig x -> Expr11 sig a) -> Result11 sig a
check_result11 (NoOp11 v) k _ = k v
check_result11 (Op11 op x_op) _ x_op' = Op11 op (x_op' . x_op)

eval11 :: Expr11 sig a -> Result11 sig a
eval11 (Let11 ev body) =
  check_result11 (eval11 ev)
    (\v -> eval11 (body v))
    (\t -> Let11 t body)
eval11 (OpCall11 op) = Op11 op Lit11
eval11 (Handle11 h@(Handler11 ops ret) eb) =
  case eval11 eb of
    NoOp11 bv -> eval11 (ret bv)
    Op11 (Inl op) x_op -> eval11 (ops op (\y -> (Handle11 h (x_op y))))
    Op11 (Inr op) x_op -> Op11 op ((\t -> Handle11 h t) . x_op)
eval11 (Lit11 v) = NoOp11 v




-- 7. Move handle into function, just like app, binop, etc.

-- Values, including value types needed to demonstrate evaler capabilities
data Handler12 eff r a w where
  Handler12 :: (forall x. eff x -> (x -> Expr12 r w) -> Expr12 r w)
            -> (a -> Expr12 r w)
            -> Handler12 eff r a w

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr12 sig a where
  Let12 :: Expr12 sig x -> (x -> Expr12 sig a) -> Expr12 sig a
  OpCall12 :: sig a -> Expr12 sig a
--  Handle12 :: Handler12 eff r a w -> Expr12 (eff :++: r) a -> Expr12 r w
  Lit12 :: a -> Expr12 sig a

data Result12 sig a where
  NoOp12 :: a -> Result12 sig a
  Op12 :: sig x -> (x -> Expr12 sig a) -> Result12 sig a


app12 :: Expr12 sig (x -> Expr12 sig a) -> Expr12 sig x -> Expr12 sig a
app12 ef ea =
  Let12 ef (\body ->
    Let12 ea (\va -> body va))

pair12 :: Expr12 sig x -> Expr12 sig y -> Expr12 sig (x, y)
pair12 e1 e2 =
  Let12 e1 (\v1 ->
    Let12 e2 (\v2 -> Lit12 (v1, v2)))

cons12 :: Expr12 sig x -> Expr12 sig [x] -> Expr12 sig [x]
cons12 e es =
  Let12 e (\v ->
    Let12 es (\vs ->
      Lit12 (v : vs)))

list12 :: [Expr12 sig x] -> Expr12 sig [x]
list12 es = lettify_list12 es []

unOp12 :: (x -> a) -> Expr12 sig x -> Expr12 sig a
unOp12 uop e =
  Let12 e (\v ->
    Lit12 (uop v))

binOp12 :: Expr12 sig x -> (x -> y -> a) -> Expr12 sig y -> Expr12 sig a
binOp12 e1 bop e2 =
  Let12 e1 (\v1 ->
    Let12 e2 (\v2 -> Lit12 (bop v1 v2)))

if12 :: Expr12 sig Bool -> Expr12 sig a -> Expr12 sig a -> Expr12 sig a
if12 ec et ee =
  Let12 ec (\b -> if b then et else ee)

op12 :: eff :<<: sig => (x -> eff a) -> Expr12 sig x -> Expr12 sig a
op12 op e = Let12 e (OpCall12 . inj . op)

handle12 :: Handler12 eff r a w -> Expr12 (eff :++: r) a -> Expr12 r w
handle12 h@(Handler12 ops ret) eb = case eb of
  Lit12 bv -> ret bv
  Let12 (OpCall12 (Inl op)) body -> ops op (\y -> (handle12 h (body y)))
  Let12 (OpCall12 (Inr op)) body -> Let12 (OpCall12 op) ((\t -> handle12 h t) . body)
  Let12 (Lit12 bv) body -> handle12 h (body bv) -- Unnecessary let
  Let12 (Let12 e' body') body -> handle12 h (Let12 e' (\v' -> Let12 (body' v') body)) -- Let-normalization, should be avoided if possible
  OpCall12 op -> handle12 h (Let12 (OpCall12 op) Lit12) -- Just a standard wrapping of OpCalls as Lets
-- Force the structure of the Let-tree here (x can contain different trees still, but we'll limit it to only
-- contain operations, merging Let and OpCall into one).

handle11 :: Handler11 eff r a w -> Expr11 (eff :++: r) a -> Expr11 r w
handle11 h@(Handler11 ops ret) eb = case eb of
  Lit11 bv -> ret bv
  Let11 (OpCall11 (Inl op)) body -> ops op (\y -> (handle11 h (body y)))
  Let11 (OpCall11 (Inr op)) body -> Let11 (OpCall11 op) ((\t -> handle11 h t) . body)
  Let11 (Lit11 bv) body -> handle11 h (body bv)
  Let11 (Let11 e' body') body -> handle11 h (Let11 e' (\v' -> Let11 (body' v') body))
  OpCall11 op -> handle11 h (Let11 (OpCall11 op) Lit11)


eval11_1 :: Expr11 sig a -> Result11 sig a
eval11_1 (Handle11 h@(Handler11 ops ret) eb) = eval11 (handle11 h eb)
eval11_2 (Handle11 h@(Handler11 ops ret) eb) = eval11 (case eb of
  Lit11 bv -> ret bv
  Let11 (OpCall11 (Inl op)) body -> ops op (\y -> (handle11 h (body y)))
  Let11 (OpCall11 (Inr op)) body -> Let11 (OpCall11 op) ((\t -> handle11 h t) . body)
  Let11 (Lit11 bv) body -> handle11 h (body bv)
  Let11 (Let11 e' body') body -> handle11 h (Let11 e' (\v' -> Let11 (body' v') body))
  OpCall11 op -> handle11 h (Let11 (OpCall11 op) Lit11))
eval11_3 (Handle11 h@(Handler11 ops ret) eb) = case eb of
  Lit11 bv -> eval11 (ret bv)
  Let11 (OpCall11 (Inl op)) body -> eval11 (ops op (\y -> (handle11 h (body y))))
  Let11 (OpCall11 (Inr op)) body -> eval11 (Let11 (OpCall11 op) ((\t -> handle11 h t) . body))
  Let11 (Lit11 bv) body -> eval11 (handle11 h (body bv))
  Let11 (Let11 e' body') body -> eval11 (handle11 h (Let11 e' (\v' -> Let11 (body' v') body)))
  OpCall11 op -> eval11 (handle11 h (Let11 (OpCall11 op) Lit11))
eval11_4 (Handle11 h@(Handler11 ops ret) eb) = case eb of
  Lit11 bv -> eval11 (ret bv)
  Let11 (OpCall11 (Inl op)) body -> eval11 (ops op (\y -> (handle11 h (body y))))
  Let11 (OpCall11 (Inr op)) body -> check_result11 (eval11 (OpCall11 op))
                                      (\v -> eval11 (handle11 h (body v)))
                                      (\t -> Let11 t (\v -> handle11 h (body v)))
  Let11 (Lit11 bv) body -> eval11 (handle11 h (body bv))
  Let11 (Let11 e' body') body -> eval11 (handle11 h (Let11 e' (\v' -> Let11 (body' v') body)))
  OpCall11 op -> eval11 (handle11 h (Let11 (OpCall11 op) Lit11))
eval11_5 (Handle11 h@(Handler11 ops ret) eb) = case eb of
  Lit11 bv -> eval11 (ret bv)
  Let11 (OpCall11 (Inl op)) body -> eval11 (ops op (\y -> (handle11 h (body y))))
--  Let11 (OpCall11 (Inr op)) body -> check_result11 (Op11 op Lit11)
--                                      (\v -> eval11 (handle11 h (body v)))
--                                      (\t -> Let11 t (\v -> handle11 h (body v)))
--  Let11 (OpCall11 (Inr op)) body -> Op11 op ((\t -> Let11 t (\v -> handle11 h (body v))) . Lit11)
--  Let11 (OpCall11 (Inr op)) body -> Op11 op (\t -> Let11 (Lit11 t) (\v -> handle11 h (body v)))
--  Let11 (OpCall11 (Inr op)) body -> Op11 op (\v -> handle11 h (body v))
  Let11 (OpCall11 (Inr op)) body -> Op11 op ((\t -> handle11 h t) . body)
  Let11 (Lit11 bv) body -> eval11 (handle11 h (body bv))
  Let11 (Let11 e' body') body -> eval11 (handle11 h (Let11 e' (\v' -> Let11 (body' v') body)))
--  OpCall11 op -> eval11 (handle11 h (Let11 (OpCall11 op) Lit11))
  OpCall11 op -> eval11 (handle11 h (Let11 (OpCall11 op) Lit11))

--check_result11 :: Result11 sig x -> (x -> Result11 sig a) -> (Expr11 sig x -> Expr11 sig a) -> Result11 sig a
--check_result11 (NoOp11 v) k _ = k v
--check_result11 (Op11 op x_op) _ x_op' = Op11 op (x_op' . x_op)

--eval11
--  :: Expr11 sig a
--  -> Result11 sig a
--eval11 (Let11 ev body) =
--  check_result11 (eval11 ev)
--    (\v -> eval11 (body v))
--    (\t -> Let11 t body)
--eval11 (OpCall11 op) = Op11 op Lit11
--eval11 (Handle11 h@(Handler11 ops ret) eb) =
--  case eval11 eb of
--    NoOp11 bv -> eval11 (ret bv)
--    Op11 (Inl op) x_op -> eval11 (ops op (\y -> (Handle11 h (x_op y))))
--    Op11 (Inr op) x_op -> Op11 op ((\t -> Handle11 h t) . x_op)
--eval11 (Lit11 v) = NoOp11 v


check_result12 :: Result12 sig x -> (x -> Result12 sig a) -> (Expr12 sig x -> Expr12 sig a) -> Result12 sig a
check_result12 (NoOp12 v) k _ = k v
check_result12 (Op12 op x_op) _ x_op' = Op12 op (x_op' . x_op)

lettify_list12
  :: [Expr12 sig a]
  -> [a]
  -> Expr12 sig [a]
lettify_list12 [] vs = Lit12 vs
lettify_list12 (e : es) vs = Let12 e (\v -> lettify_list12 es (vs <> [v]))

data EPure a

run12 :: Expr12 EPure a -> a
run12 (Let12 ev body) = run12 (body (run12 ev))
run12 (Lit12 v) = v

eval12
  :: Expr12 sig a
  -> Result12 sig a
eval12 (Let12 ev body) =
  check_result12 (eval12 ev)
    (\v -> eval12 (body v))
    (\t -> Let12 t body)
eval12 (OpCall12 op) = Op12 op Lit12
eval12 (Lit12 v) = NoOp12 v



-- 8. Realize that the structure Lets requires us to think differently, so merge Op and Let cases.
data Handler13 eff r a w where
  Handler13 :: (forall x. eff x -> (x -> Expr13 r w) -> Expr13 r w)
            -> (a -> Expr13 r w)
            -> Handler13 eff r a w

-- Expressions needed to demonstrate algebraic effects and handlers
data Expr13 sig a where
  OpLet13 :: sig x -> (x -> Expr13 sig a) -> Expr13 sig a
  Lit13 :: a -> Expr13 sig a

instance Functor (Expr13 sig) where
  fmap = liftM

instance Applicative (Expr13 sig) where
  pure = Lit13
  (<*>) = ap

--instance Monad (Expr13 sig) where
--  return = Lit13
--  (>>=) = let13

instance Monad (Expr13 sig) where
  return = pure
  Lit13 x >>= body = body x
  OpLet13 op k >>= body = OpLet13 op (\x -> k x >>= body)

data Result13 sig a where
  NoOp13 :: a -> Result13 sig a
  Op13 :: sig x -> (x -> Expr13 sig a) -> Result13 sig a


let13 :: Expr13 sig x -> (x -> Expr13 sig a) -> Expr13 sig a
let13 (Lit13 x) body = body x
let13 (OpLet13 op k) body = OpLet13 op (\x -> let13 (k x) body)

app13 :: Expr13 sig (x -> Expr13 sig a) -> Expr13 sig x -> Expr13 sig a
app13 ef ea = do
  body <- ef
  va <- ea
  body va

pair13 :: Expr13 sig x -> Expr13 sig y -> Expr13 sig (x, y)
pair13 e1 e2 =
  let13 e1 (\v1 ->
    let13 e2 (\v2 -> Lit13 (v1, v2)))

cons13 :: Expr13 sig x -> Expr13 sig [x] -> Expr13 sig [x]
cons13 e es =
  let13 e (\v ->
    let13 es (\vs ->
      Lit13 (v : vs)))

list13 :: [Expr13 sig x] -> Expr13 sig [x]
list13 [] = Lit13 []
list13 (e : es) = let13 e (\v -> let13 (list13 es) (\vs -> Lit13 (v : vs)))

unOp13 :: (x -> a) -> Expr13 sig x -> Expr13 sig a
unOp13 uop e =
  let13 e (\v ->
    Lit13 (uop v))

binOp13 :: Expr13 sig x -> (x -> y -> a) -> Expr13 sig y -> Expr13 sig a
binOp13 e1 bop e2 =
  let13 e1 (\v1 ->
    let13 e2 (\v2 -> Lit13 (bop v1 v2)))

if13 :: Expr13 sig Bool -> Expr13 sig a -> Expr13 sig a -> Expr13 sig a
if13 ec et ee =
  let13 ec (\b -> if b then et else ee)

op13 :: eff :<<: sig => (x -> eff a) -> Expr13 sig x -> Expr13 sig a
op13 op e = let13 e (\x -> OpLet13 (inj $ op x) Lit13)

handle13 :: Handler13 eff r a w -> Expr13 (eff :++: r) a -> Expr13 r w
handle13 h@(Handler13 ops ret) eb = case eb of
  Lit13 bv -> ret bv
  OpLet13 (Inl op) k -> ops op (\y -> (handle13 h (k y)))
  OpLet13 (Inr op) k -> OpLet13 op ((\t -> handle13 h t) . k)

run13 :: Expr13 EPure a -> a
run13 (Lit13 v) = v

eval13
  :: Expr13 sig a
  -> Result13 sig a
eval13 (OpLet13 op body) = Op13 op body
eval13 (Lit13 v) = NoOp13 v







-- 9. Notice this is the freer monad lol
data Handler14 eff r a w where
  Handler14 :: (forall x. eff x -> (x -> Freer r w) -> Freer r w)
            -> (a -> Freer r w)
            -> Handler14 eff r a w

-- Expressions needed to demonstrate algebraic effects and handlers
data Freer sig a where
  Impure :: sig x -> (x -> Freer sig a) -> Freer sig a
  Pure :: a -> Freer sig a

instance Functor (Freer sig) where
  fmap = liftM

instance Applicative (Freer sig) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer sig) where
  return = pure
  Pure v >>= k = k v
  Impure op k' >>= k = Impure op (\v -> k' v >>= k)

data Result14 sig a where
  NoOp14 :: a -> Result14 sig a
  Op14 :: sig x -> (x -> Freer sig a) -> Result14 sig a


let14 :: Freer sig x -> (x -> Freer sig a) -> Freer sig a
let14 = (>>=)

app14 :: Freer sig (x -> Freer sig a) -> Freer sig x -> Freer sig a
app14 ef ea = do
  body <- ef
  va <- ea
  body va

pair14 :: Freer sig x -> Freer sig y -> Freer sig (x, y)
pair14 e1 e2 =
  let14 e1 (\v1 ->
    let14 e2 (\v2 -> return (v1, v2)))

cons14 :: Freer sig x -> Freer sig [x] -> Freer sig [x]
cons14 e es =
  let14 e (\v ->
    let14 es (\vs ->
      return (v : vs)))

list14 :: [Freer sig x] -> Freer sig [x]
list14 [] = return []
list14 (e : es) = do
  v <- e
  vs <- list14 es
  return (v : vs)

unOp14 :: (x -> a) -> Freer sig x -> Freer sig a
unOp14 uop e =
  let14 e (\v ->
    return (uop v))

binOp14 :: Freer sig x -> (x -> y -> a) -> Freer sig y -> Freer sig a
binOp14 e1 bop e2 =
  let14 e1 (\v1 ->
    let14 e2 (\v2 -> return (bop v1 v2)))

if14 :: Freer sig Bool -> Freer sig a -> Freer sig a -> Freer sig a
if14 ec et ee =
  let14 ec (\b -> if b then et else ee)

op14 :: eff :<<: sig => (x -> eff a) -> Freer sig x -> Freer sig a
op14 op e = let14 e (\x -> Impure (inj $ op x) return)

handle14 :: Handler14 eff r a w -> Freer (eff :++: r) a -> Freer r w
handle14 h@(Handler14 ops ret) eb = case eb of
  Pure bv -> ret bv
  Impure (Inl op) k -> ops op (\y -> (handle14 h (k y)))
  Impure (Inr op) k -> Impure op ((\t -> handle14 h t) . k)

eval14
  :: Freer sig a
  -> Result14 sig a
eval14 (Impure op body) = Op14 op body
eval14 (Pure v) = NoOp14 v

