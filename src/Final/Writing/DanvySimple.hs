module Final.Writing.DanvySimple where

data Type
  = IntT
  | FunT Type Type
  deriving (Eq, Show)

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

lambda :: String -> Expr -> Expr
lambda x eb = Lit (LambdaV x eb)

int :: Int -> Expr
int = Lit . IntV

data PotentialRedex
  = PRBeta String Expr Value
  | PRLet String Expr Value
  | PRAdd Value Value
  | PRMul Value Value
  | PRError String
  deriving (Show)

data ContractumOrError
  = Contractum Expr
  | Error String
  deriving (Show)

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

contract :: PotentialRedex -> ContractumOrError
contract (PRBeta x e v) = Contractum (subst x v e)
contract (PRLet x e v) = Contractum (subst x v e)
contract (PRAdd (IntV n1) (IntV n2)) = Contractum (Closed (IntV (n1 + n2)))
contract (PRMul (IntV n1) (IntV n2)) = Contractum (Closed (IntV (n1 * n2)))
contract (PRError err) = Error err
contract pr = Error ("Cannot match types for: " <> show pr)

data Context
  = CEmpty
  | CAppL Context Expr
  | CAppR Value Context
  | CLet String Context Expr
  | CBinOpL Context BinOpOperator Expr
  | CBinOpR Value BinOpOperator Context
  deriving (Show)

recompose :: Context -> Expr -> Expr
recompose CEmpty t = t
recompose (CAppL c e2) t = recompose c $ App t e2
recompose (CAppR v1 c) t = recompose c $ App (Closed v1) t
recompose (CLet x c e) t = recompose c $ Let x t e
recompose (CBinOpL c bop e2) t = recompose c $ BinOp t bop e2
recompose (CBinOpR v1 bop c) t = recompose c $ BinOp (Closed v1) bop t

data ValueOrDecomposition
  = VODValue Value
  | VODDec PotentialRedex Context
  deriving (Show)

data Result
  = Result Value
  | Wrong String
  deriving (Show, Eq)

decompose_expr :: Context -> Expr -> ValueOrDecomposition
decompose_expr c (Var s) =
  VODDec (PRError ("Free variable: " <> s)) c
decompose_expr c (App e1 e2) =
  decompose_expr (CAppL c e2) e1
decompose_expr c (Let x ev eb) =
  decompose_expr (CLet x c eb) ev
decompose_expr c (BinOp e1 bop e2) =
  decompose_expr (CBinOpL c bop e2) e1
decompose_expr c (Lit v) =
  decompose_context v c
decompose_expr c (Closed v) =
  decompose_context v c

decompose_context :: Value -> Context -> ValueOrDecomposition
decompose_context v CEmpty =
  VODValue v
decompose_context v (CAppL c e2) =
  decompose_expr (CAppR v c) e2
decompose_context v (CAppR (LambdaV x e) c) =
  VODDec (PRBeta x e v) c
decompose_context _ (CAppR v1 c) =
  VODDec (PRError ("Cannot apply non-function value: " <> show v1)) c
decompose_context v (CLet x c eb) =
  VODDec (PRLet x eb v) c
decompose_context v1 (CBinOpL c bop e2) =
  decompose_expr (CBinOpR v1 bop c) e2
decompose_context v2 (CBinOpR v1 Add c) =
  VODDec (PRAdd v1 v2) c
decompose_context v2 (CBinOpR v1 Mul c) =
  VODDec (PRMul v1 v2) c

decompose :: Expr -> ValueOrDecomposition
decompose = decompose_expr CEmpty

iterate0 :: ValueOrDecomposition -> Result
iterate0 (VODValue v) = Result v
iterate0 (VODDec pr c) = case contract pr of
  Contractum e -> iterate0 (decompose (recompose c e))
  Error err -> Wrong err

normalise0 :: Expr -> Result
normalise0 e = iterate0 (decompose e)

---------------------------------------------------------------
---- Refocus
---------------------------------------------------------------
refocus :: Context -> Expr -> ValueOrDecomposition
refocus = decompose_expr

iterate1 :: ValueOrDecomposition -> Result
iterate1 (VODValue v) = Result v
iterate1 (VODDec pr c) = case contract pr of
  Contractum e -> iterate1 (refocus c e)
  Error err -> Wrong err

normalise1 :: Expr -> Result
normalise1 e = iterate1 (decompose e)

---------------------------------------------------------------
---- Inlining contraction
---------------------------------------------------------------
iterate2 :: ValueOrDecomposition -> Result
iterate2 (VODValue v) = Result v
iterate2 (VODDec (PRBeta x e v) c) = iterate2 $ refocus c (subst x v e)
iterate2 (VODDec (PRLet x e v) c) = iterate2 $ refocus c (subst x v e)
iterate2 (VODDec (PRAdd (IntV n1) (IntV n2)) c) = iterate2 $ refocus c (Closed (IntV (n1 + n2)))
iterate2 (VODDec (PRMul (IntV n1) (IntV n2)) c) = iterate2 $ refocus c (Closed (IntV (n1 * n2)))
iterate2 (VODDec (PRError err) _) = Wrong err
iterate2 (VODDec pr _) = Wrong ("Cannot match types for: " <> show pr)

normalise2 :: Expr -> Result
normalise2 = iterate2 . refocus CEmpty

---------------------------------------------------------------
---- Lightweight fusion
---------------------------------------------------------------
refocus_expr3 :: Context -> Expr -> Result
refocus_expr3 c (Var s) =
  iterate3 $ VODDec (PRError ("Free variable: " <> s)) c
refocus_expr3 c (App e1 e2) =
  refocus_expr3 (CAppL c e2) e1
refocus_expr3 c (Let x ev eb) =
  refocus_expr3 (CLet x c eb) ev
refocus_expr3 c (BinOp e1 bop e2) =
  refocus_expr3 (CBinOpL c bop e2) e1
refocus_expr3 c (Lit v) =
  refocus_context3 v c
refocus_expr3 c (Closed v) =
  refocus_context3 v c

refocus_context3 :: Value -> Context -> Result
refocus_context3 v CEmpty =
  iterate3 $ VODValue v
refocus_context3 v (CAppL c e2) =
  refocus_expr3 (CAppR v c) e2
refocus_context3 v (CAppR (LambdaV x e) c) =
  iterate3 $ VODDec (PRBeta x e v) c
refocus_context3 _ (CAppR v' c) =
  iterate3 $
    VODDec
      ( PRError
          ( "Cannot apply non-function value: " <> show v'
          )
      )
      c
refocus_context3 v (CLet x c eb) =
  iterate3 $ VODDec (PRLet x eb v) c
refocus_context3 v1 (CBinOpL c bop e2) =
  refocus_expr3 (CBinOpR v1 bop c) e2
refocus_context3 v2 (CBinOpR v1 Add c) =
  iterate3 $ VODDec (PRAdd v1 v2) c
refocus_context3 v2 (CBinOpR v1 Mul c) =
  iterate3 $ VODDec (PRMul v1 v2) c

iterate3 :: ValueOrDecomposition -> Result
iterate3 (VODValue v) = Result v
iterate3 (VODDec (PRBeta x e v) c) = refocus_expr3 c (subst x v e)
iterate3 (VODDec (PRLet x e v) c) = refocus_expr3 c (subst x v e)
iterate3 (VODDec (PRAdd (IntV n1) (IntV n2)) c) = refocus_expr3 c (Closed (IntV (n1 + n2)))
iterate3 (VODDec (PRMul (IntV n1) (IntV n2)) c) = refocus_expr3 c (Closed (IntV (n1 * n2)))
iterate3 (VODDec (PRError err) _) = Wrong err
iterate3 (VODDec pr _) = Wrong ("Cannot match types for: " <> show pr)

normalise3 :: Expr -> Result
normalise3 = refocus_expr3 CEmpty

---------------------------------------------------------------
---- Corridor transitions
---------------------------------------------------------------
refocus_expr4 :: Context -> Expr -> Result
refocus_expr4 _ (Var s) =
  Wrong ("Free variable: " <> s)
refocus_expr4 c (App e1 e2) =
  refocus_expr4 (CAppL c e2) e1
refocus_expr4 c (Let x ev eb) =
  refocus_expr4 (CLet x c eb) ev
refocus_expr4 c (BinOp e1 bop e2) =
  refocus_expr4 (CBinOpL c bop e2) e1
refocus_expr4 c (Lit v) =
  refocus_context4 v c
refocus_expr4 c (Closed v) =
  refocus_context4 v c

refocus_context4 :: Value -> Context -> Result
refocus_context4 v CEmpty =
  Result v
refocus_context4 v (CAppL c e2) =
  refocus_expr4 (CAppR v c) e2
refocus_context4 v (CAppR (LambdaV x e) c) =
  refocus_expr4 c (subst x v e)
refocus_context4 _ (CAppR v1 _) =
  Wrong ("Cannot apply non-function value: " <> show v1)
refocus_context4 v (CLet x c eb) =
  refocus_expr4 c (subst x v eb)
refocus_context4 v1 (CBinOpL c bop e2) =
  refocus_expr4 (CBinOpR v1 bop c) e2
refocus_context4 (IntV n2) (CBinOpR (IntV n1) Add c) =
  refocus_expr4 c (Closed (IntV (n1 + n2)))
refocus_context4 (IntV n2) (CBinOpR (IntV n1) Mul c) =
  refocus_expr4 c (Closed (IntV (n1 * n2)))
refocus_context4 _ (CBinOpR _ bop _) =
  Wrong ("Cannot match types for binary operation: " <> show bop)

iterate4 :: ValueOrDecomposition -> Result
iterate4 (VODValue _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRBeta _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRLet _ _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRAdd _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRMul _ _) _) = Wrong "DEAD CLAUSE"
iterate4 (VODDec (PRError _) _) = Wrong "DEAD CLAUSE"

normalise4 :: Expr -> Result
normalise4 = refocus_expr4 CEmpty

---------------------------------------------------------------
---- Renaming transition functions and flattening configurations
---------------------------------------------------------------
eval5 :: Context -> Expr -> Result
eval5 _ (Var s) = Wrong ("Free variable: " <> s)
eval5 c (App e1 e2) = eval5 (CAppL c e2) e1
eval5 c (Let x ev eb) = eval5 (CLet x c eb) ev
eval5 c (BinOp e1 bop e2) = eval5 (CBinOpL c bop e2) e1
eval5 c (Lit v) = continue5 v c
eval5 c (Closed v) = continue5 v c

continue5 :: Value -> Context -> Result
continue5 v CEmpty = Result v
continue5 v (CAppL c e2) = eval5 (CAppR v c) e2
continue5 v (CAppR (LambdaV x e) c) = eval5 c (subst x v e)
continue5 _ (CAppR v1 _) =
  Wrong ("Cannot apply non-function value: " <> show v1)
continue5 v (CLet x c eb) = eval5 c (subst x v eb)
continue5 v1 (CBinOpL c bop e2) = eval5 (CBinOpR v1 bop c) e2
continue5 (IntV n2) (CBinOpR (IntV n1) Add c) = eval5 c (Closed (IntV (n1 + n2)))
continue5 (IntV n2) (CBinOpR (IntV n1) Mul c) = eval5 c (Closed (IntV (n1 * n2)))
continue5 _ (CBinOpR _ bop _) = Wrong ("Cannot match types for binary operation: " <> show bop)

normalise5 :: Expr -> Result
normalise5 = eval5 CEmpty

---------------------------------------------------------------
---- Refunctionalisation
---------------------------------------------------------------
eval6 :: Expr -> (Value -> Result) -> Result
eval6 (Var s) _ = Wrong ("Free variable: " <> s)
eval6 (App e1 e2) k =
  eval6
    e1
    ( \v1 ->
        eval6
          e2
          ( \v2 ->
              case v1 of
                LambdaV x e -> eval6 (subst x v2 e) k
                _ -> Wrong ("Cannot apply non-function value: " <> show v1)
          )
    )
eval6 (Let x ev eb) k =
  eval6
    ev
    ( \v ->
        eval6 (subst x v eb) k
    )
eval6 (BinOp e1 bop e2) k =
  eval6
    e1
    ( \v1 ->
        eval6
          e2
          ( \v2 -> case (v1, bop, v2) of
              (IntV n1, Add, IntV n2) -> eval6 (Closed (IntV (n1 + n2))) k
              (IntV n1, Mul, IntV n2) -> eval6 (Closed (IntV (n1 * n2))) k
              _ -> Wrong ("Cannot match types for binary operation: " <> show bop)
          )
    )
eval6 (Lit v) k = k v
eval6 (Closed v) k = k v

normalise6 :: Expr -> Result
normalise6 e = eval6 e Result

---------------------------------------------------------------
---- Back to direct style
---------------------------------------------------------------
check_result7 :: Result -> (Value -> Result) -> Result
check_result7 (Result v) k = k v
check_result7 err _ = err

eval7' :: Expr -> Result
eval7' (Var s) = Wrong ("Free variable: " <> s)
eval7' (App e1 e2) =
  case eval7 e1 of
    Result v1 -> case eval7 e2 of
      Result v2 -> case v1 of
        LambdaV x e -> eval7 (subst x v2 e)
        _ -> Wrong ("Cannot apply non-function value: " <> show v1)
      err -> err
    err -> err
eval7' (Let x ev eb) =
  case eval7 ev of
    Result v -> eval7 (subst x v eb)
    err -> err
eval7' (BinOp e1 bop e2) =
  case eval7 e1 of
    Result v1 -> case eval7 e2 of
      Result v2 -> case (v1, bop, v2) of
        (IntV n1, Add, IntV n2) -> eval7 (Closed (IntV (n1 + n2)))
        (IntV n1, Mul, IntV n2) -> eval7 (Closed (IntV (n1 * n2)))
        _ -> Wrong ("Cannot match types for binary operation: " <> show bop)
      err -> err
    err -> err
eval7' (Lit v) = Result v
eval7' (Closed v) = Result v

eval7 :: Expr -> Result
eval7 (Var s) = Wrong ("Free variable: " <> s)
eval7 (App e1 e2) =
  check_result7
    (eval7 e1)
    ( \v1 ->
        check_result7
          (eval7 e2)
          ( \v2 ->
              case v1 of
                LambdaV x e -> eval7 (subst x v2 e)
                _ -> Wrong ("Cannot apply non-function value: " <> show v1)
          )
    )
eval7 (Let x ev eb) =
  check_result7
    (eval7 ev)
    ( \v ->
        eval7 (subst x v eb)
    )
eval7 (BinOp e1 bop e2) =
  check_result7
    (eval7 e1)
    ( \v1 ->
        check_result7
          (eval7 e2)
          ( \v2 -> case (v1, bop, v2) of
              (IntV n1, Add, IntV n2) -> eval7 (Closed (IntV (n1 + n2)))
              (IntV n1, Mul, IntV n2) -> eval7 (Closed (IntV (n1 * n2)))
              _ -> Wrong ("Cannot match types for binary operation: " <> show bop)
          )
    )
eval7 (Lit v) = Result v
eval7 (Closed v) = Result v

normalise7 :: Expr -> Result
normalise7 = eval7
