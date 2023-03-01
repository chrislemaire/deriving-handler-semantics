{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Final.ProgramGen where

import Control.Monad (forM)
import Control.Monad.State (StateT (..), evalStateT, get, modify, runStateT)
import Data.Maybe (isNothing, maybeToList)
import Final.TestUtil
import GHC.OldList (nub)
import Test.QuickCheck.Gen (Gen (..), chooseInt)
import Test.QuickCheck.GenT

data Suspended a = Suspended {unSuspend :: a}
  deriving (Show, Eq)

data Type
  = FunT Type EType
  | SFunT Type SEType
  | IntT
  | BoolT
  | UnitT
  | PairT Type Type
  | ListT Type
  | VarT Int
  | SumT Type Type
  | SuspendedT [EffType] Type
  | SSuspendedT [ScopedEffType] Type
  deriving (Eq, Show)

data EType = EType [EffType] Type
  deriving (Eq, Show)

data SEType = SEType {setEffs :: [ScopedEffType], setT :: Type}
  deriving (Eq, Show)

data EffType = EffType Int [OpType] RetType Bool
  deriving (Eq, Show)

data ScopedEffType = ScopedEffType
  { setSIdx :: Int,
    setSFTVar :: Int,
    setSFT :: Type,
    setSRetT :: SRetType,
    setSOpTs :: [OpType],
    setSScopeTs :: [ScopeType],
    setSMendT :: MendType,
    setSIsAllowed :: Bool
  }
  deriving (Eq, Show)

data OpType = OpType
  { opSIdx :: Int,
    opSArgVar :: Int,
    opSArgT :: Type,
    opSResT :: Type
  }
  deriving (Show, Eq)

data ScopeType = ScopeType
  { scpSIdx :: Int,
    scpSArgVar :: Int,
    scpSArgT :: Type,
    scpSRecVar :: Int,
    scpSResT :: Type
  }
  deriving (Show, Eq)

data RetType = RetType
  { retSArgVar :: Int,
    retSArgTIdx :: Int,
    retSNv :: [Type],
    retSArgT :: Type,
    retSRetT :: EType
  }
  deriving (Show, Eq)

data SRetType = SRetType
  { sretSArgVar :: Int,
    sretSArgTIdx :: Int,
    sretSNv :: [Type],
    sretSArgT :: Type,
    sretSRetT :: SEType
  }
  deriving (Show, Eq)

data MendType = MendType
  { mendSArgVar :: Int,
    mendSArgTIdx :: Int,
    mendSArgT :: Type,
    mendSResVar :: Int,
    mendSRetT :: Type
  }
  deriving (Show, Eq)

data Value
  = LambdaV Int Expr
  | IntV Int
  | BoolV Bool
  | UnitV
  | PairV Value Value
  | NilV
  | ConsV Value Value
  | SumLeftV Value
  | SumRightV Value
  | SuspendedV (Suspended Expr)
  deriving (Show, Eq)

data Handler = Handler Int [OpI] RetI
  deriving (Show, Eq)

data OpI = OpI
  { opISig :: OpType,
    opIBody :: Expr
  }
  deriving (Show, Eq)

data RetI = RetI
  { retISig :: RetType,
    retIBody :: Expr
  }
  deriving (Show, Eq)

data SRetI = SRetI
  { sretISig :: SRetType,
    sretIBody :: Expr
  }
  deriving (Show, Eq)

data ShallowHandler = ShallowHandler Int [OpI] RetI
  deriving (Show, Eq)

data ScopedHandler = ScopedHandler Int ScopedEffType SRetI [OpI] [ScpI] MendI
  deriving (Show, Eq)

data ScpI = ScpI
  { scpISig :: ScopeType,
    scpIBody :: Expr
  }
  deriving (Show, Eq)

data MendI = MendI
  { mendISig :: MendType,
    mendIBody :: Expr
  }
  deriving (Show, Eq)

data UnOpOperator
  = Fst
  | Snd
  deriving (Bounded, Enum, Show, Eq)

data BinOpOperator
  = Concat
  | Add
  | Mul
  deriving (Bounded, Enum, Show, Eq)

data Case
  = ConstC Value
  | VarC String
  | NilC
  | ConsC Case Case
  | PairC Case Case
  | DataC String Case
  deriving (Show, Eq)

data Expr
  = Var Int
  | App Expr Expr
  | Let Int Expr Expr
  | OpCall Int Int Expr
  | Handle Handler Expr
  | ScopedHandle ScopedHandler Expr
  | Lit Value
  | If Expr Expr Expr
  | Pair Expr Expr
  | Cons Expr Expr
  | Resume Expr
  | Hdl
  | UnOp UnOpOperator Expr
  | BinOp Expr BinOpOperator Expr
  | --
    ScopeCall Int Int Expr Int Expr
  | --
    UnSum Expr (Int, Expr) (Int, Expr)
  | UnList Expr Expr (Int, Int, Expr)
  deriving (Show, Eq)

-----------------------------------------------------
---- Extractors for a part of the environment
-----------------------------------------------------
varsOfType :: [Type] -> Type -> [(Type, Int)]
varsOfType nv ty =
  filter (\(ty', _) -> ty == ty') $
    zip nv [0 ..]

opsOfType :: [EffType] -> Type -> [(EffType, OpType)]
opsOfType nv ty = do
  effT@(EffType _ ops _ isAllowed) <- nv
  opT@(OpType _ _ _ retT) <- ops

  [(effT, opT) | ty == retT, isAllowed]

sopsOfType :: [ScopedEffType] -> Type -> [(ScopedEffType, OpType)]
sopsOfType nv ty = do
  effT@(ScopedEffType {..}) <- nv
  opT@(OpType _ _ _ retT) <- setSOpTs

  [(effT, opT) | ty == retT, setSIsAllowed]

-----------------------------------------------------
---- Helper functions for generation
-----------------------------------------------------
replaceTVar :: Int -> Type -> Type -> Type
replaceTVar n withT (VarT n')
  | n == n' = withT
  | otherwise = VarT n'
replaceTVar n withT (ListT t) = ListT (replaceTVar n withT t)
replaceTVar n withT (PairT t1 t2) = PairT (replaceTVar n withT t1) (replaceTVar n withT t2)
replaceTVar n withT (FunT t1 (EType effs t2)) = FunT (replaceTVar n withT t1) (EType effs (replaceTVar n withT t2))
replaceTVar n withT (SFunT t1 (SEType effs t2)) = SFunT (replaceTVar n withT t1) (SEType effs (replaceTVar n withT t2))
replaceTVar n withT (SumT t1 t2) = SumT (replaceTVar n withT t1) (replaceTVar n withT t2)
replaceTVar n withT (SuspendedT effs t) = SuspendedT effs (replaceTVar n withT t)
replaceTVar n withT (SSuspendedT effs t) = SSuspendedT effs (replaceTVar n withT t)
replaceTVar _ _ t = t

insertTVar :: MonadGen g => Int -> Type -> Maybe Type -> g (Type, Maybe Type)
insertTVar n t@(ListT tx) mt =
  frequency $
    [ ( 1,
        do
          (tx', m) <- insertTVar n tx mt
          return (ListT tx', m)
      )
    ]
      <> [(2, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t@(PairT t1 t2) mt =
  frequency $
    [ ( 1,
        do
          (t1', m1) <- insertTVar n t1 mt
          (t2', m2) <- insertTVar n t2 m1
          return (PairT t1' t2', m2)
      )
    ]
      <> [(1, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t@(FunT t1 (EType effs t2)) mt =
  frequency $
    [ ( 1,
        do
          (t2', m2) <- insertTVar n t2 mt
          return (FunT t1 (EType effs t2'), m2)
      )
    ]
      <> [(2, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t@(SFunT t1 (SEType effs t2)) mt =
  frequency $
    [ ( 1,
        do
          (t2', m2) <- insertTVar n t2 mt
          return (SFunT t1 (SEType effs t2'), m2)
      )
    ]
      <> [(2, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t@(SumT t1 t2) mt =
  frequency $
    [ ( 1,
        do
          (t1', m1) <- insertTVar n t1 mt
          (t2', m2) <- insertTVar n t2 m1
          return (SumT t1' t2', m2)
      )
    ]
      <> [(2, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t@(SuspendedT effs tx) mt =
  frequency $
    [ ( 1,
        do
          (tx', m) <- insertTVar n tx mt
          return (SuspendedT effs tx', m)
      )
    ]
      <> [(2, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t@(SSuspendedT effs tx) mt =
  frequency $
    [ ( 1,
        do
          (tx', m) <- insertTVar n tx mt
          return (SSuspendedT effs tx', m)
      )
    ]
      <> [(2, return (VarT n, Just t)) | isNothing mt || mt == Just t]
insertTVar n t mt =
  frequency $
    [(1, return (t, mt))]
      <> [(1, return (VarT n, Just t)) | isNothing mt || mt == Just t]

collectTVars :: Type -> [Int]
collectTVars = nub . go
  where
    go (VarT n) = [n]
    go (ListT t) = collectTVars t
    go (PairT t1 t2) = collectTVars t1 <> collectTVars t2
    go (FunT t1 (EType _ t2)) = collectTVars t1 <> collectTVars t2
    go (SFunT t1 (SEType _ t2)) = collectTVars t1 <> collectTVars t2
    go (SumT t1 t2) = collectTVars t1 <> collectTVars t2
    go (SuspendedT _ t) = collectTVars t
    go (SSuspendedT _ t) = collectTVars t
    go _ = []

-----------------------------------------------------
---- Generators and arbitraries
-----------------------------------------------------
genType :: Bool -> Bool -> MGen Type
genType isScoped eqOnly = sized arb
  where
    arb :: Int -> MGen Type
    arb 0 =
      frequency
        [ (8, return IntT),
          (2, return UnitT)
        ]
    -- (1, VarT <$> chooseInt (1, usedTVars))
    arb n =
      frequency $
        [ (1, return IntT),
          (1, return UnitT),
          (3, ListT <$> arb (n `div` 4)),
          (3, PairT <$> arb (n `div` 5) <*> arb (n `div` 5))
        ]
          <> [(3, SumT <$> arb (n `div` 3) <*> arb (n `div` 3)) | isScoped]
          <> [(2, FunT <$> arb (n `div` 6) <*> (EType [] <$> arb (n `div` 4))) | not eqOnly && not isScoped]
          <> [(2, SFunT <$> arb (n `div` 6) <*> (SEType [] <$> arb (n `div` 4))) | not eqOnly && isScoped]

genListLitValue :: MGen Value -> MGen Value
genListLitValue childG = do
  sz <- liftGen $ chooseInt (0, 4)
  arb sz
  where
    arb :: Int -> MGen Value
    arb 0 = return NilV
    arb n = ConsV <$> childG <*> arb (n - 1)

arbDeepExpr :: [EffType] -> [Type] -> Int -> Type -> Int -> MGen Expr
arbDeepExpr effs nv tVars ty n
  | n == 0 =
      frequencyM $
        [(1, genLitValue nv tVars ty)]
          <> ((\(_, idx) -> (1, Just $ return (Var idx))) <$> varsOfType nv ty)
  | otherwise =
      frequencyM $
        ((\(_, idx) -> (20, Just $ return (Var idx))) <$> varsOfType nv ty)
          -- app
          <> [ ( 2,
                 Just $ do
                   argT <- genType False False
                   funE <- arbDeepExpr effs nv tVars (FunT argT (EType effs ty)) (n `div` 4)
                   argE <- arbDeepExpr effs nv tVars argT (n `div` 4)
                   return $ App funE argE
               )
             ]
          -- let
          <> [ ( 5,
                 Just $ do
                   argT <- genType False False
                   argE <- arbDeepExpr effs nv tVars argT (n `div` 4)
                   bodyE <- arbDeepExpr effs (nv <> [argT]) tVars ty (n `div` 4)
                   return $ Let (length nv) argE bodyE
               )
             ]
          -- op-call
          <> ( ( \(EffType effIdx _ _ _, OpType opIdx _ argT _) ->
                   ( 100,
                     Just $ do
                       argE <- arbDeepExpr effs nv tVars argT (n `div` 4)
                       return $ OpCall effIdx opIdx argE
                   )
               )
                 <$> opsOfType effs ty
             )
          -- handle
          <> [ ( 7,
                 Just $ do
                   (ty', ct) <- insertTVar tVars ty Nothing
                   nOps <- liftGen $ chooseInt (1, 3)

                   effIdx <- get
                   modify (+ 1)

                   opITs <- sequence $ (\opIdx -> OpType opIdx (length nv) <$> genType False False <*> genType False False) <$> [1 .. nOps]
                   let retIT = RetType (length nv) tVars nv (maybe (VarT (tVars + 1)) (const $ VarT tVars) ct) (EType effs ty')
                   let effT = EffType effIdx opITs retIT

                   opIs <-
                     sequence $
                       ( \opT@(OpType _ _ argT retT) ->
                           OpI opT <$> arbOpExpr ty' argT retT
                       )
                         <$> opITs
                   retI <- RetI retIT <$> arbDeepExpr effs (nv <> [VarT tVars]) (tVars + 1) ty' (n `div` 4)

                   bodyT <- maybe (genType False False) return ct
                   bodyE <- arbDeepExpr (effs <> [effT True]) nv tVars bodyT (n `div` 4)

                   return $ Handle (Handler effIdx opIs retI) bodyE
               )
             ]
          -- literals
          <> [(5, genLitValue nv tVars ty)]
          -- lambda-expressions
          <> [ ( 7,
                 withFunT
                   ( \argT (EType effs' retT) -> do
                       bodyE <- arbDeepExpr effs' (nv <> [argT]) tVars retT (n `div` 2)
                       return $ Lit $ LambdaV (length nv) bodyE
                   )
               )
             ]
          -- pair-expressions
          <> [ ( 3,
                 withPairT
                   ( \t1 t2 -> do
                       e1 <- arbDeepExpr effs nv tVars t1 (n `div` 4)
                       e2 <- arbDeepExpr effs nv tVars t2 (n `div` 4)
                       return $ Pair e1 e2
                   )
               )
             ]
          -- list-expressions
          <> [ ( 2,
                 withListT genListExpr
               )
             ]
          -- un-ops
          <> [ ( 2,
                 Just $ do
                   otherT <- genType False False
                   (unOp, pairT) <- elements [(Fst, PairT ty otherT), (Snd, PairT otherT ty)]
                   pairE <- arbDeepExpr effs nv tVars pairT (n `div` 2)
                   return $ UnOp unOp pairE
               )
             ]
          -- bin-ops
          <> [ ( 5,
                 withIntT $ do
                   binOp <- elements [Add, Mul]
                   e1 <- arbDeepExpr effs nv tVars IntT (n `div` 4)
                   e2 <- arbDeepExpr effs nv tVars IntT (n `div` 4)
                   return $ BinOp e1 binOp e2
               )
             ]
          <> [ ( 5,
                 withListT
                   ( \t -> do
                       e1 <- arbDeepExpr effs nv tVars (ListT t) (n `div` 4)
                       e2 <- arbDeepExpr effs nv tVars (ListT t) (n `div` 4)
                       return $ BinOp e1 Concat e2
                   )
               )
             ]
          -- if-expressions
          <> [ ( 4,
                 Just $ do
                   cE <- arbDeepExpr effs nv tVars BoolT (n `div` 3)
                   tE <- arbDeepExpr effs nv tVars ty (n `div` 3)
                   eE <- arbDeepExpr effs nv tVars ty (n `div` 3)
                   return $ If cE tE eE
               )
             ]
  where
    withFunT :: (Type -> EType -> MGen Expr) -> Maybe (MGen Expr)
    withFunT f = case ty of
      FunT argT retT -> Just $ f argT retT
      _ -> Nothing

    withPairT :: (Type -> Type -> MGen Expr) -> Maybe (MGen Expr)
    withPairT f = case ty of
      PairT t1 t2 -> Just $ f t1 t2
      _ -> Nothing

    withListT :: (Type -> MGen Expr) -> Maybe (MGen Expr)
    withListT f = case ty of
      ListT t -> Just $ f t
      _ -> Nothing

    withIntT :: MGen Expr -> Maybe (MGen Expr)
    withIntT g = case ty of
      IntT -> Just g
      _ -> Nothing

    genListExpr :: Type -> MGen Expr
    genListExpr t = do
      sz <- liftGen $ chooseInt (0, 4)
      arb sz
      where
        arb :: Int -> MGen Expr
        arb 0 = arbDeepExpr effs nv tVars (ListT t) (n `div` 6)
        arb sz = Cons <$> arbDeepExpr effs nv tVars t (n `div` 4) <*> arb (sz - 1)

    arbOpExpr :: Type -> Type -> Type -> MGen Expr
    arbOpExpr ty' argT retT = arbOpComb n True
      where
        arbEmpty :: Type -> MMGen Expr
        arbEmpty ty'' = genLitValue (nv <> [argT]) (tVars + 1) ty''

        arbKCall :: Int -> MMGen Expr
        arbKCall n = Just $ do
          kArgE <- arbDeepExpr effs (nv <> [argT]) (tVars + 1) retT (n `div` 2)
          return $ Resume kArgE

        arbOpComb :: Int -> Bool -> MGen Expr
        arbOpComb 0 _ = frequencyM [(5, arbEmpty ty'), (3, arbKCall n)]
        arbOpComb n b =
          frequencyM
            [ (3, arbKCall n),
              (2, arbEmpty ty'),
              ( 5,
                if not b
                  then Nothing
                  else Just $ do
                    nGen <- liftGen $ chooseInt (0, 3)
                    es <- forM [0 .. nGen] (const $ arbOpComb (n `div` 4) False)
                    e <- arbDeepExpr effs (nv <> replicate nGen ty') (tVars + 1) ty' (n `div` 2)
                    return $ snd $ foldr (\ea (nVars, e') -> (nVars + 1, Let nVars ea e')) (length nv, e) es
              )
            ]

    genLitValue :: [Type] -> Int -> Type -> MMGen Expr
    genLitValue nv tVars = \ty ->
      let litG = arb ty
       in case litG of
            [] -> Nothing
            _ -> Just $ oneof litG
      where
        arbV :: Type -> MMGen Value
        arbV ty = case ty of
          IntT -> return $ IntV <$> liftGen (chooseInt (-200, 200))
          BoolT -> return $ oneOfFail $ return . BoolV <$> [True, False]
          UnitT -> return $ return UnitV
          (FunT argT (EType effs retT)) ->
            return $
              LambdaV (length nv)
                <$> arbDeepExpr effs (nv <> [argT]) tVars retT 0
          (PairT t1 t2) -> do
            v1 <- arbV t1
            v2 <- arbV t2
            return $ PairV <$> v1 <*> v2
          (ListT t) -> do
            g <- arbV t
            Just $ genListLitValue g
          SuspendedT effs' t ->
            return $
              (SuspendedV . Suspended) <$> arbDeepExpr effs' nv tVars t n
          _ -> Nothing

        arb :: Type -> [MGen Expr]
        arb ty = maybeToList (fmap Lit <$> arbV ty) <> ((\(_, idx) -> return (Var idx)) <$> varsOfType nv ty)

arbShallowExpr :: [EffType] -> [Type] -> Int -> Type -> Int -> MGen Expr
arbShallowExpr effs nv tVars ty n
  | n == 0 =
      frequencyM $
        [(1, genLitValue nv tVars ty)]
          <> ((\(_, idx) -> (1, Just $ return (Var idx))) <$> varsOfType nv ty)
  | otherwise =
      frequencyM $
        ((\(_, idx) -> (20, Just $ return (Var idx))) <$> varsOfType nv ty)
          -- app
          <> [ ( 2,
                 Just $ do
                   argT <- genType False False
                   funE <- arbShallowExpr effs nv tVars (FunT argT (EType effs ty)) (n `div` 4)
                   argE <- arbShallowExpr effs nv tVars argT (n `div` 4)
                   return $ App funE argE
               )
             ]
          -- let
          <> [ ( 5,
                 Just $ do
                   argT <- genType False False
                   argE <- arbShallowExpr effs nv tVars argT (n `div` 4)
                   bodyE <- arbShallowExpr effs (nv <> [argT]) tVars ty (n `div` 4)
                   return $ Let (length nv) argE bodyE
               )
             ]
          -- op-call
          <> ( ( \(EffType effIdx _ _ _, OpType opIdx _ argT _) ->
                   ( 100,
                     Just $ do
                       argE <- arbShallowExpr effs nv tVars argT (n `div` 4)
                       return $ OpCall effIdx opIdx argE
                   )
               )
                 <$> opsOfType effs ty
             )
          -- handle
          <> [ ( 7,
                 withoutSuspendT $ do
                   (ty', ct) <- insertTVar tVars ty Nothing
                   nOps <- liftGen $ chooseInt (1, 3)

                   effIdx <- get
                   modify (+ 1)

                   opITs <- sequence $ (\opIdx -> OpType opIdx (length nv) <$> genType False False <*> genType False False) <$> [1 .. nOps]
                   let retIT = RetType (length nv) tVars nv (maybe (VarT (tVars + 1)) (const $ VarT tVars) ct) (EType effs ty')
                   let effT = EffType effIdx opITs retIT

                   opIs <-
                     sequence $
                       ( \opT@(OpType _ _ argT retT) ->
                           OpI opT <$> arbOpExpr (effT False) ty' argT retT
                       )
                         <$> opITs
                   retI <- RetI retIT <$> arbShallowExpr effs (nv <> [VarT tVars]) (tVars + 1) ty' (n `div` 4)

                   bodyT <- SuspendedT (effs <> [effT True]) <$> maybe (genType False False) return ct
                   bodyE <- arbShallowExpr effs nv tVars bodyT (n `div` 4)

                   return $ Handle (Handler effIdx opIs retI) bodyE
               )
             ]
          -- literals
          <> [(5, genLitValue nv tVars ty)]
          -- lambda-expressions
          <> [ ( 7,
                 withFunT
                   ( \argT (EType effs' retT) -> do
                       bodyE <- arbShallowExpr effs' (nv <> [argT]) tVars retT (n `div` 2)
                       return $ Lit $ LambdaV (length nv) bodyE
                   )
               )
             ]
          -- pair-expressions
          <> [ ( 3,
                 withPairT
                   ( \t1 t2 -> do
                       e1 <- arbShallowExpr effs nv tVars t1 (n `div` 4)
                       e2 <- arbShallowExpr effs nv tVars t2 (n `div` 4)
                       return $ Pair e1 e2
                   )
               )
             ]
          -- list-expressions
          <> [ ( 2,
                 withListT genListExpr
               )
             ]
          -- un-ops
          <> [ ( 2,
                 withoutSuspendT $ do
                   otherT <- genType False False
                   (unOp, pairT) <- elements [(Fst, PairT ty otherT), (Snd, PairT otherT ty)]
                   pairE <- arbShallowExpr effs nv tVars pairT (n `div` 2)
                   return $ UnOp unOp pairE
               )
             ]
          -- bin-ops
          <> [ ( 5,
                 withIntT $ do
                   binOp <- elements [Add, Mul]
                   e1 <- arbShallowExpr effs nv tVars IntT (n `div` 4)
                   e2 <- arbShallowExpr effs nv tVars IntT (n `div` 4)
                   return $ BinOp e1 binOp e2
               )
             ]
          <> [ ( 5,
                 withListT
                   ( \t -> do
                       e1 <- arbShallowExpr effs nv tVars (ListT t) (n `div` 4)
                       e2 <- arbShallowExpr effs nv tVars (ListT t) (n `div` 4)
                       return $ BinOp e1 Concat e2
                   )
               )
             ]
          -- if-expressions
          <> [ ( 4,
                 Just $ do
                   cE <- arbShallowExpr effs nv tVars BoolT (n `div` 10)
                   tE <- arbShallowExpr effs nv tVars ty (n `div` 6)
                   eE <- arbShallowExpr effs nv tVars ty (n `div` 6)
                   return $ If cE tE eE
               )
             ]
  where
    withFunT :: (Type -> EType -> MGen Expr) -> Maybe (MGen Expr)
    withFunT f = case ty of
      FunT argT retT -> Just $ f argT retT
      _ -> Nothing

    withPairT :: (Type -> Type -> MGen Expr) -> Maybe (MGen Expr)
    withPairT f = case ty of
      PairT t1 t2 -> Just $ f t1 t2
      _ -> Nothing

    withListT :: (Type -> MGen Expr) -> Maybe (MGen Expr)
    withListT f = case ty of
      ListT t -> Just $ f t
      _ -> Nothing

    withIntT :: MGen Expr -> Maybe (MGen Expr)
    withIntT g = case ty of
      IntT -> Just g
      _ -> Nothing

    withoutSuspendT :: MGen Expr -> Maybe (MGen Expr)
    withoutSuspendT g = case ty of
      SuspendedT _ _ -> Nothing
      _ -> Just g

    genListExpr :: Type -> MGen Expr
    genListExpr t = do
      sz <- liftGen $ chooseInt (0, 4)
      arb sz
      where
        arb :: Int -> MGen Expr
        arb 0 = arbShallowExpr effs nv tVars (ListT t) (n `div` 6)
        arb sz = Cons <$> arbShallowExpr effs nv tVars t (n `div` 4) <*> arb (sz - 1)

    arbOpExpr :: EffType -> Type -> Type -> Type -> MGen Expr
    arbOpExpr effT ty' argT retT = arbOpComb n
      where
        arbEmpty :: Type -> MMGen Expr
        arbEmpty ty'' = genLitValue (nv <> [argT]) (tVars + 1) ty''

        arbKCall :: Int -> MMGen Expr
        arbKCall n = Just $ do
          kArgE <- arbShallowExpr (effs <> [effT]) (nv <> [argT]) (tVars + 1) retT (n `div` 2)
          return $ App Hdl $ Lit $ SuspendedV $ Suspended $ Resume kArgE

        arbOpComb :: Int -> MGen Expr
        arbOpComb 0 = frequencyM [(5, arbEmpty ty'), (3, arbKCall n)]
        arbOpComb n =
          frequencyM
            [ (3, arbKCall n),
              (2, arbEmpty ty'),
              ( 5,
                Just $ do
                  nGen <- liftGen $ chooseInt (0, 3)
                  es <- forM [0 .. nGen] (const $ arbOpComb (n `div` 4))
                  e <- arbShallowExpr effs (nv <> replicate nGen ty') (tVars + 1) ty' (n `div` 2)
                  return $ snd $ foldr (\ea (nVars, e') -> (nVars + 1, Let nVars ea e')) (length nv, e) es
              )
            ]

    genLitValue :: [Type] -> Int -> Type -> MMGen Expr
    genLitValue nv tVars = \ty ->
      let litG = arb ty
       in case litG of
            [] -> Nothing
            _ -> Just $ oneof litG
      where
        arbV :: Type -> MMGen Value
        arbV ty = case ty of
          IntT -> return $ IntV <$> liftGen (chooseInt (-200, 200))
          BoolT -> return $ oneOfFail $ return . BoolV <$> [True, False]
          UnitT -> return $ return UnitV
          (FunT argT (EType effs retT)) ->
            return $
              LambdaV (length nv)
                <$> arbShallowExpr effs (nv <> [argT]) tVars retT 0
          (PairT t1 t2) -> do
            v1 <- arbV t1
            v2 <- arbV t2
            return $ PairV <$> v1 <*> v2
          (ListT t) -> do
            g <- arbV t
            Just $ genListLitValue g
          SuspendedT effs' t ->
            return $
              (SuspendedV . Suspended) <$> arbShallowExpr effs' nv tVars t n
          _ -> Nothing

        arb :: Type -> [MGen Expr]
        arb ty = maybeToList (fmap Lit <$> arbV ty) <> ((\(_, idx) -> return (Var idx)) <$> varsOfType nv ty)

arbScopedExpr :: [ScopedEffType] -> [Type] -> Int -> Type -> Int -> MGen Expr
arbScopedExpr effs nv tVars ty n
  | n == 0 =
      frequencyM $
        [(1, genLitValue nv tVars ty)]
          <> ((\(_, idx) -> (1, Just $ return (Var idx))) <$> varsOfType nv ty)
  | otherwise =
      frequencyM $
        ((\(_, idx) -> (20, Just $ return (Var idx))) <$> varsOfType nv ty)
          -- app
          <> [ ( 2,
                 Just $ do
                   argT <- genType True False
                   funE <- arbScopedExpr effs nv tVars (SFunT argT (SEType effs ty)) (n `div` 4)
                   argE <- arbScopedExpr effs nv tVars argT (n `div` 4)
                   return $ App funE argE
               )
             ]
          -- let
          <> [ ( 5,
                 Just $ do
                   argT <- genType True False
                   argE <- arbScopedExpr effs nv tVars argT (n `div` 4)
                   bodyE <- arbScopedExpr effs (nv <> [argT]) tVars ty (n `div` 4)
                   return $ Let (length nv) argE bodyE
               )
             ]
          -- op-call
          <> ( ( \(ScopedEffType {..}, OpType opIdx _ argT _) ->
                   ( 100,
                     Just $ do
                       argE <- arbScopedExpr effs nv tVars argT (n `div` 4)
                       return $ OpCall setSIdx opIdx argE
                   )
               )
                 <$> sopsOfType effs ty
             )
          -- handle
          <> [ ( 7,
                 Just $ do
                   (ty', ct) <- insertTVar tVars ty Nothing
                   nOps <- liftGen $ chooseInt (1, 3)

                   effIdx <- get
                   modify (+ 1)

                   opITs <- sequence $ (\opIdx -> OpType opIdx (length nv) <$> genType True False <*> genType True False) <$> [1 .. nOps]
                   let retIT = SRetType (length nv) tVars nv (maybe (VarT (tVars + 1)) (const $ VarT tVars) ct) (SEType effs ty')
                   let mendIT = MendType (length nv) tVars (VarT tVars) (length nv + 1) ty'

                   let effT = ScopedEffType effIdx tVars ty' retIT opITs [] mendIT

                   opIs <-
                     sequence $
                       ( \opT@(OpType _ _ argT retT) ->
                           OpI opT <$> arbOpExpr ty' argT retT
                       )
                         <$> opITs
                   retI <- SRetI retIT <$> arbScopedExpr effs (nv <> [VarT tVars]) (tVars + 1) ty' (n `div` 4)

                   bodyT <- maybe (genType True False) return ct
                   bodyE <- arbScopedExpr (effs <> [effT True]) nv tVars bodyT (n `div` 4)

                   let scpIs = []

                   mendI <-
                     MendI mendIT
                       <$> arbScopedExpr
                         effs
                         ( nv
                             <> [ replaceTVar tVars (VarT (tVars + 1)) ty',
                                  SFunT (VarT (tVars + 1)) (SEType (effs <> [effT True]) (replaceTVar tVars (VarT (tVars + 2)) ty'))
                                ]
                         )
                         (tVars + 3)
                         (replaceTVar tVars (VarT (tVars + 2)) ty')
                         (n `div` 4)

                   return $ ScopedHandle (ScopedHandler effIdx (effT False) retI opIs scpIs mendI) bodyE
               )
             ]
          -- literals
          <> [(5, genLitValue nv tVars ty)]
          -- lambda-expressions
          <> [ ( 7,
                 withFunT
                   ( \argT (SEType effs' retT) -> do
                       bodyE <- arbScopedExpr effs' (nv <> [argT]) tVars retT (n `div` 2)
                       return $ Lit $ LambdaV (length nv) bodyE
                   )
               )
             ]
          -- pair-expressions
          <> [ ( 3,
                 withPairT
                   ( \t1 t2 -> do
                       e1 <- arbScopedExpr effs nv tVars t1 (n `div` 4)
                       e2 <- arbScopedExpr effs nv tVars t2 (n `div` 4)
                       return $ Pair e1 e2
                   )
               )
             ]
          -- list-expressions
          <> [ ( 2,
                 withListT genListExpr
               )
             ]
          -- un-ops
          <> [ ( 2,
                 Just $ do
                   otherT <- genType True False
                   (unOp, pairT) <- elements [(Fst, PairT ty otherT), (Snd, PairT otherT ty)]
                   pairE <- arbScopedExpr effs nv tVars pairT (n `div` 2)
                   return $ UnOp unOp pairE
               )
             ]
          -- bin-ops
          <> [ ( 5,
                 withIntT $ do
                   binOp <- elements [Add, Mul]
                   e1 <- arbScopedExpr effs nv tVars IntT (n `div` 4)
                   e2 <- arbScopedExpr effs nv tVars IntT (n `div` 4)
                   return $ BinOp e1 binOp e2
               )
             ]
          <> [ ( 5,
                 withListT
                   ( \t -> do
                       e1 <- arbScopedExpr effs nv tVars (ListT t) (n `div` 4)
                       e2 <- arbScopedExpr effs nv tVars (ListT t) (n `div` 4)
                       return $ BinOp e1 Concat e2
                   )
               )
             ]
          -- if-expressions
          <> [ ( 4,
                 Just $ do
                   cE <- arbScopedExpr effs nv tVars BoolT (n `div` 10)
                   tE <- arbScopedExpr effs nv tVars ty (n `div` 6)
                   eE <- arbScopedExpr effs nv tVars ty (n `div` 6)
                   return $ If cE tE eE
               )
             ]
          -- un-sums
          <> [ ( 7,
                 Just $ do
                   t1 <- genType True False
                   t2 <- genType True False

                   e <- arbScopedExpr effs nv tVars (SumT t1 t2) (n `div` 12)
                   ex <- arbScopedExpr effs (nv <> [t1]) tVars ty (n `div` 12)
                   ey <- arbScopedExpr effs (nv <> [t2]) tVars ty (n `div` 12)

                   return $ UnSum e (length nv, ex) (length nv, ey)
               )
             ]
          -- un-lists
          <> [ ( 3,
                 Just $ do
                   t <- genType True False

                   e <- arbScopedExpr effs nv tVars (ListT t) (n `div` 12)
                   en <- arbScopedExpr effs (nv) tVars ty (n `div` 12)
                   ec <- arbScopedExpr effs (nv <> [t, ListT t]) tVars ty (n `div` 12)

                   return $ UnList e en (length nv, length nv + 1, ec)
               )
             ]
  where
    withFunT :: (Type -> SEType -> MGen Expr) -> Maybe (MGen Expr)
    withFunT f = case ty of
      SFunT argT retT -> Just $ f argT retT
      _ -> Nothing

    withPairT :: (Type -> Type -> MGen Expr) -> Maybe (MGen Expr)
    withPairT f = case ty of
      PairT t1 t2 -> Just $ f t1 t2
      _ -> Nothing

    withListT :: (Type -> MGen Expr) -> Maybe (MGen Expr)
    withListT f = case ty of
      ListT t -> Just $ f t
      _ -> Nothing

    withIntT :: MGen Expr -> Maybe (MGen Expr)
    withIntT g = case ty of
      IntT -> Just g
      _ -> Nothing

    genListExpr :: Type -> MGen Expr
    genListExpr t = do
      sz <- liftGen $ chooseInt (0, 4)
      arb sz
      where
        arb :: Int -> MGen Expr
        arb 0 = arbScopedExpr effs nv tVars (ListT t) (n `div` 6)
        arb sz = Cons <$> arbScopedExpr effs nv tVars t (n `div` 4) <*> arb (sz - 1)

    arbOpExpr :: Type -> Type -> Type -> MGen Expr
    arbOpExpr ty' argT retT = arbOpComb n
      where
        arbEmpty :: Type -> MMGen Expr
        arbEmpty ty'' = genLitValue (nv <> [argT]) (tVars + 1) ty''

        arbKCall :: Int -> MMGen Expr
        arbKCall n = Just $ do
          kArgE <- arbScopedExpr effs (nv <> [argT]) (tVars + 1) retT (n `div` 2)
          return $ Resume kArgE

        arbOpComb :: Int -> MGen Expr
        arbOpComb 0 = frequencyM [(5, arbEmpty ty'), (3, arbKCall n)]
        arbOpComb n =
          frequencyM
            [ (3, arbKCall n),
              (2, arbEmpty ty'),
              ( 5,
                Just $ do
                  nGen <- liftGen $ chooseInt (0, 3)
                  es <- forM [0 .. nGen] (const $ arbOpComb (n `div` 4))
                  e <- arbScopedExpr effs (nv <> replicate nGen ty') (tVars + 1) ty' (n `div` 2)
                  return $ snd $ foldr (\ea (nVars, e') -> (nVars + 1, Let nVars ea e')) (length nv, e) es
              )
            ]

    genLitValue :: [Type] -> Int -> Type -> MMGen Expr
    genLitValue nv tVars = \ty ->
      let litG = arb ty
       in case litG of
            [] -> Nothing
            _ -> Just $ oneof litG
      where
        arb :: Type -> [MGen Expr]
        arb ty = maybeToList (fmap Lit <$> genValue nv tVars ty) <> ((\(_, idx) -> return (Var idx)) <$> varsOfType nv ty)

    genValue :: [Type] -> Int -> Type -> MMGen Value
    genValue nv tVars = arbV
      where
        arbV :: Type -> MMGen Value
        arbV ty = case ty of
          IntT -> return $ IntV <$> liftGen (chooseInt (-200, 200))
          BoolT -> return $ oneOfFail $ return . BoolV <$> [True, False]
          UnitT -> return $ return UnitV
          (SFunT argT (SEType effs retT)) ->
            return $
              LambdaV (length nv)
                <$> arbScopedExpr effs (nv <> [argT]) tVars retT 0
          (PairT t1 t2) -> do
            v1 <- arbV t1
            v2 <- arbV t2
            return $ PairV <$> v1 <*> v2
          (ListT t) -> do
            g <- arbV t
            Just $ genListLitValue g
          (SumT t1 t2) -> frequencyMM [(1, fmap SumLeftV <$> arbV t1), (1, fmap SumRightV <$> arbV t2)]
          SSuspendedT effs' t ->
            return $
              (SuspendedV . Suspended) <$> arbScopedExpr effs' nv tVars t n
          _ -> Nothing

data TypeAndExpr = TypeAndExpr Type Expr

arbitraryType :: Bool -> Gen Type
arbitraryType isScoped = do
  may <- runGenT $ flip evalStateT 0 $ genType isScoped True
  maybe (arbitraryType isScoped) return may

arbitraryDeepExpr :: Gen Expr
arbitraryDeepExpr = (\(TypeAndExpr _ e) -> e) <$> arbitraryTypeAndDeepExpr

arbitraryTypeAndDeepExpr :: Gen TypeAndExpr
arbitraryTypeAndDeepExpr = do
  ty <- arbitraryType False
  e <- go ty
  return $ TypeAndExpr ty e
  where
    go :: Type -> Gen Expr
    go ty = do
      may <- runGenT $ flip evalStateT 0 $ sized (arbDeepExpr [] [] 0 ty)
      maybe (go ty) return may

arbitraryShallowExpr :: Gen Expr
arbitraryShallowExpr = (\(TypeAndExpr _ e) -> e) <$> arbitraryTypeAndShallowExpr

arbitraryTypeAndShallowExpr :: Gen TypeAndExpr
arbitraryTypeAndShallowExpr = do
  ty <- arbitraryType False
  e <- go ty
  return $ TypeAndExpr ty e
  where
    go :: Type -> Gen Expr
    go ty = do
      may <- runGenT $ flip evalStateT 0 $ sized (arbShallowExpr [] [] 0 ty)
      maybe (go ty) return may

arbitraryScopedExpr :: Gen Expr
arbitraryScopedExpr = (\(TypeAndExpr _ e) -> e) <$> arbitraryTypeAndScopedExpr

arbitraryTypeAndScopedExpr :: Gen TypeAndExpr
arbitraryTypeAndScopedExpr = do
  ty <- arbitraryType True
  e <- go ty
  return $ TypeAndExpr ty e
  where
    go :: Type -> Gen Expr
    go ty = do
      may <- runGenT $ flip evalStateT 0 $ sized (arbScopedExpr [] [] 0 ty)
      maybe (go ty) return may
