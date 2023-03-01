{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE UndecidableInstances #-}

module Final.SmallToDeepTest where

import Control.Exception (displayException, throw)
import Control.Monad.State
import Data.Char (isDigit)
import Data.Map hiding (drop, foldl, foldr)
import Final.ProgramGen as PG
import qualified Final.SmallToDeep as STD
import Final.TestUtil (programRunsTheSameProperty, disableLongTests)
import Language.Haskell.Interpreter
import Language.Haskell.Interpreter.Extension
import Language.Haskell.TH
import qualified Language.Haskell.TH.Syntax as TH
import Test.QuickCheck.Property (exception, liftBool)
import qualified Test.QuickCheck.Property as QC
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.QuickCheck hiding (elements)
import UnliftIO.Directory (createDirectoryIfMissing, doesFileExist, removeFile)

instance Eq STD.Result7 where
  STD.NoOp7 v1 == STD.NoOp7 v2 = v1 == v2
  _ == _ = False

instance Eq STD.Value8 where
  STD.IntV8 n1 == STD.IntV8 n2 = n1 == n2
  STD.BoolV8 b1 == STD.BoolV8 b2 = b1 == b2
  STD.UnitV8 == STD.UnitV8 = True
  STD.PairV8 v1 v2 == STD.PairV8 v1' v2' = v1 == v1' && v2 == v2'
  STD.NilV8 == STD.NilV8 = True
  STD.ConsV8 v1 v2 == STD.ConsV8 v1' v2' = v1 == v1' && v2 == v2'
  _ == _ = False

instance Eq STD.Result8 where
  STD.NoOp8 v1 == STD.NoOp8 v2 = v1 == v2
  _ == _ = False

instance Eq STD.Value9 where
  STD.IntV9 n1 == STD.IntV9 n2 = n1 == n2
  STD.BoolV9 b1 == STD.BoolV9 b2 = b1 == b2
  STD.UnitV9 == STD.UnitV9 = True
  STD.PairV9 v1 v2 == STD.PairV9 v1' v2' = v1 == v1' && v2 == v2'
  STD.NilV9 == STD.NilV9 = True
  STD.ConsV9 v1 v2 == STD.ConsV9 v1' v2' = v1 == v1' && v2 == v2'
  _ == _ = False

instance Eq STD.Result9 where
  STD.NoOp9 v1 == STD.NoOp9 v2 = v1 == v2
  _ == _ = False

---------------------------------------------------------------
---- The list of tests to run
---------------------------------------------------------------
tests :: TestTree
tests =
  testGroup
    "Small to Deep conversion"
    [ testGroup
        "Program Generator"
        [ disableLongTests $ testProperty
            "Program generation does not cause failure (big)"
            (withMaxSuccess 5000 $ programNeverErrorsProperty 100),
          testProperty
            "Program generation does not cause failure (small)"
            (withMaxSuccess 100000 $ programNeverErrorsProperty 12)
        ],
      testGroup
        "Generated"
        [ testProperty
            "Equivalence of normalise0 and normalise1"
            (programRunsTheSameProperty id STD.normalise0 STD.normalise1 expr0Gen),
          testProperty
            "Equivalence of normalise0 and normalise2"
            (programRunsTheSameProperty id STD.normalise0 STD.normalise2 expr0Gen),
          testProperty
            "Equivalence of normalise0 and normalise3"
            (programRunsTheSameProperty id STD.normalise0 STD.normalise3 expr0Gen),
          testProperty
            "Equivalence of normalise0 and normalise4"
            (programRunsTheSameProperty id STD.normalise0 STD.normalise4 expr0Gen),
          testProperty
            "Equivalence of normalise0 and normalise5"
            (programRunsTheSameProperty id STD.normalise0 STD.normalise5 expr0Gen),
          testProperty
            "Equivalence of normalise0 and normalise6"
            (programRunsTheSameProperty id STD.normalise0 STD.normalise6 expr0Gen),
          testProperty
            "Equivalence of normalise0 and eval7"
            (programRunsTheSameProperty id (convertResult0To7 . STD.normalise0) STD.eval7 expr0Gen),
          testProperty
            "Equivalence of normalise0 and eval8"
            (programRunsTheSameProperty (convertExpr0To8 empty) (convertResult7To8 . convertResult0To7 . STD.normalise0) STD.eval8 expr0Gen),
          testProperty
            "Equivalence of normalise0 and eval9"
            ( programRunsTheSameProperty (convertExpr0To9 empty) (convertResult0To9 . STD.normalise0) STD.eval9 expr0Gen
            ),
          disableLongTests $  testGroup
            "Equivalence of programs that need to be resynthesized"
            [ testProperty
                "Equivalence of normalise0 and eval10"
                (withMaxSuccess bigTestRepetitions $ testMany10 bigTestQuantity),
              testProperty
                "Equivalence of normalise0 and eval11"
                (withMaxSuccess bigTestRepetitions $ testMany11 bigTestQuantity),
              testProperty
                "Equivalence of normalise0 and eval12"
                (withMaxSuccess bigTestRepetitions $ testMany12 bigTestQuantity),
              testProperty
                "Equivalence of normalise0 and eval13"
                (withMaxSuccess bigTestRepetitions $ testMany13 bigTestQuantity),
              testProperty
                "Equivalence of normalise0 and eval14"
                (withMaxSuccess bigTestRepetitions $ testMany14 bigTestQuantity)
            ]
        ],
      testGroup
        "Manual"
        [ testCase "Normalise0 yields expected result" $
            void $
              traverse (\(e, v) -> STD.normalise0 e @?= STD.Result (convertToValue0 v)) ((\(TypeAndExpr _ e, v) -> (convertToExpr0 e, v)) <$> manualTestProgramsAndResults),
          testCase "Equivalence of normalise0 and normalise1" $
            void $
              traverse (\e -> STD.normalise0 e @?= STD.normalise1 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and normalise2" $
            void $
              traverse (\e -> STD.normalise0 e @?= STD.normalise2 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and normalise3" $
            void $
              traverse (\e -> STD.normalise0 e @?= STD.normalise3 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and normalise4" $
            void $
              traverse (\e -> STD.normalise0 e @?= STD.normalise4 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and normalise5" $
            void $
              traverse (\e -> STD.normalise0 e @?= STD.normalise5 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and normalise6" $
            void $
              traverse (\e -> STD.normalise0 e @?= STD.normalise6 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and eval7" $
            void $
              traverse (\e -> convertResult0To7 (STD.normalise0 e) @?= STD.eval7 e) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and eval8" $
            void $
              traverse (\e -> convertResult7To8 (convertResult0To7 (STD.normalise0 e)) @?= STD.eval8 (convertExpr0To8 empty e)) (convertToExpr0 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise0 and eval9" $
            void $
              traverse (\e -> convertResult0To9 (STD.normalise0 e) @?= STD.eval9 (convertExpr0To9 empty e)) (convertToExpr0 <$> manualTestProgramExprs),
          disableLongTests $ testGroup
            "Equivalence of programs that need to be resynthesized"
            [ testProperty
                "Equivalence of normalise0 and eval10"
                ( ioProperty $ do
                    results <- runInterpreter (testBatchInterpreter10 manualTestPrograms)
                    case results of
                      Left err -> return (property (exception (displayException err) (throw err)))
                      Right v -> return (conjoin v)
                ),
              testProperty
                "Equivalence of normalise0 and eval11"
                ( ioProperty $ do
                    results <- runInterpreter (testBatchInterpreter11 manualTestPrograms)
                    case results of
                      Left err -> return (property (exception (displayException err) (throw err)))
                      Right v -> return (conjoin v)
                ),
              testProperty
                "Equivalence of normalise0 and eval12"
                ( ioProperty $ do
                    results <- runInterpreter (testBatchInterpreter12 manualTestPrograms)
                    case results of
                      Left err -> return (property (exception (displayException err) (throw err)))
                      Right v -> return (conjoin v)
                ),
              testProperty
                "Equivalence of normalise0 and eval13"
                ( ioProperty $ do
                    results <- runInterpreter (testBatchInterpreter13 manualTestPrograms)
                    case results of
                      Left err -> return (property (exception (displayException err) (throw err)))
                      Right v -> return (conjoin v)
                ),
              testProperty
                "Equivalence of normalise0 and eval14"
                ( ioProperty $ do
                    results <- runInterpreter (testBatchInterpreter14 manualTestPrograms)
                    case results of
                      Left err -> return (property (exception (displayException err) (throw err)))
                      Right v -> return (conjoin v)
                )
            ]
        ]
    ]

bigTestQuantity :: Int
bigTestQuantity = 1000

bigTestRepetitions :: Int
bigTestRepetitions = 10

maxBatchSize :: Int
maxBatchSize = 500

---------------------------------------------------------------
---- Property to test
---------------------------------------------------------------
programNeverErrorsProperty :: Int -> Property
programNeverErrorsProperty sz =
    mapSize (const sz) $
      forAll expr0Gen $ \e -> case STD.normalise0 e of
        STD.Result _ -> True
        _ -> False

---------------------------------------------------------------
---- Manual testing programmes
---------------------------------------------------------------
manualTestProgramExprs :: [Expr]
manualTestProgramExprs = (\(TypeAndExpr _ e) -> e) <$> manualTestPrograms

manualTestPrograms :: [TypeAndExpr]
manualTestPrograms =
  [ TypeAndExpr UnitT (Lit UnitV)
  ]

manualTestProgramsAndResults :: [(TypeAndExpr, Value)]
manualTestProgramsAndResults =
  [ (TypeAndExpr UnitT (Lit UnitV), UnitV)
  ]

---------------------------------------------------------------
---- Utilities for writing conversions
---------------------------------------------------------------
toTyVarName :: Int -> String
toTyVarName idx = "x" <> show idx

toVarName :: Int -> String
toVarName idx = "v" <> show idx

toEffName :: Int -> Int -> String
toEffName tIdx effIdx = "T" <> show tIdx <> "Eff" <> show effIdx

toOpName :: Int -> Int -> Int -> String
toOpName tIdx effIdx opIdx = "T" <> show tIdx <> "Eff" <> show effIdx <> "Op" <> show opIdx

fromOpName :: String -> (Int, Int)
fromOpName opNm = (read $ takeWhile isDigit $ drop 3 opNm, read $ reverse $ takeWhile isDigit $ reverse opNm)

---------------------------------------------------------------
---- Conversion from the generator expressions to STD.Expr (0)
---------------------------------------------------------------
convertToValue0 :: Value -> STD.Value
convertToValue0 (LambdaV arg e) = STD.LambdaV (toVarName arg) (convertToExpr0 e)
convertToValue0 (IntV n) = STD.IntV n
convertToValue0 (BoolV n) = STD.BoolV n
convertToValue0 UnitV = STD.UnitV
convertToValue0 (PairV v1 v2) = STD.PairV (convertToValue0 v1) (convertToValue0 v2)
convertToValue0 NilV = STD.NilV
convertToValue0 (ConsV v1 v2) = STD.ConsV (convertToValue0 v1) (convertToValue0 v2)

convertToHandler0 :: Handler -> STD.Handler
convertToHandler0 (Handler effIdx ops (RetI (RetType rArgIdx _ _ _ _) ret)) =
  STD.Handler
    ((\(OpI (OpType opIdx argIdx _ _) e) -> STD.OpI (toOpName 0 effIdx opIdx) (toVarName argIdx) "resume" (convertToExpr0 e)) <$> ops)
    (STD.ReturnI (toVarName rArgIdx) (convertToExpr0 ret))

convertToUnOp0 :: UnOpOperator -> STD.UnOpOperator
convertToUnOp0 Fst = STD.Fst
convertToUnOp0 Snd = STD.Snd

convertToBinOp0 :: BinOpOperator -> STD.BinOpOperator
convertToBinOp0 Concat = STD.Concat
convertToBinOp0 Add = STD.Add
convertToBinOp0 Mul = STD.Mul

convertToExpr0 :: Expr -> STD.Expr
convertToExpr0 (Var idx) = STD.Var (toVarName idx)
convertToExpr0 (App e1 e2) = STD.App (convertToExpr0 e1) (convertToExpr0 e2)
convertToExpr0 (Let idx e1 e2) = STD.Let (toVarName idx) (convertToExpr0 e1) (convertToExpr0 e2)
convertToExpr0 (OpCall effIdx opIdx e) = STD.OpCall (toOpName 0 effIdx opIdx) (convertToExpr0 e)
convertToExpr0 (Handle hlr e) = STD.Handle (convertToHandler0 hlr) (convertToExpr0 e)
convertToExpr0 (Lit v) = STD.Lit (convertToValue0 v)
convertToExpr0 (If ec et ee) = STD.If (convertToExpr0 ec) (convertToExpr0 et) (convertToExpr0 ee)
convertToExpr0 (Pair e1 e2) = STD.Pair (convertToExpr0 e1) (convertToExpr0 e2)
convertToExpr0 (Cons e1 e2) = STD.Cons (convertToExpr0 e1) (convertToExpr0 e2)
convertToExpr0 (Resume e) = STD.App (STD.Var "resume") (convertToExpr0 e)
convertToExpr0 (UnOp unOp e) = STD.UnOp (convertToUnOp0 unOp) (convertToExpr0 e)
convertToExpr0 (BinOp e1 binOp e2) = STD.BinOp (convertToExpr0 e1) (convertToBinOp0 binOp) (convertToExpr0 e2)

expr0Gen :: Gen STD.Expr
expr0Gen = convertToExpr0 <$> arbitraryDeepExpr

---------------------------------------------------------------
---- Conversion from the STD.Result (0) to STD.Result7
---------------------------------------------------------------
convertResult0To7 :: STD.Result -> STD.Result7
convertResult0To7 (STD.Result v) = STD.NoOp7 v
convertResult0To7 (STD.Wrong err) = STD.Wrong7 err

---------------------------------------------------------------
---- Conversion from the STD.Result7 to STD.Result8
---------------------------------------------------------------
convertResult7To8 :: STD.Result7 -> STD.Result8
convertResult7To8 (STD.NoOp7 v) = STD.NoOp8 (convertValue0To8 empty v)

---------------------------------------------------------------
---- Conversion from the STD.Expr (0) to STD.Expr8
---------------------------------------------------------------
convertHandler0To8 :: Map String STD.Value8 -> STD.Handler -> STD.Handler8
convertHandler0To8 nv (STD.Handler ops (STD.ReturnI nmRet eRet)) =
  STD.Handler8
    ( ( \(STD.OpI opNm nmOpArg nmResume e) ->
          STD.OpI8 opNm (\vArg res' -> convertExpr0To8 (insert nmOpArg vArg $ insert nmResume (STD.LambdaV8 res') nv) e)
      )
        <$> ops
    )
    (\v -> convertExpr0To8 (insert nmRet v nv) eRet)

convertValue0To8 :: Map String STD.Value8 -> STD.Value -> STD.Value8
convertValue0To8 nv (STD.LambdaV nm e) = STD.LambdaV8 (\v -> convertExpr0To8 (insert nm v nv) e)
convertValue0To8 _ (STD.IntV i) = STD.IntV8 i
convertValue0To8 _ STD.UnitV = STD.UnitV8
convertValue0To8 _ (STD.BoolV b) = STD.BoolV8 b
convertValue0To8 nv (STD.PairV v1 v2) = STD.PairV8 (convertValue0To8 nv v1) (convertValue0To8 nv v2)
convertValue0To8 _ STD.NilV = STD.NilV8
convertValue0To8 nv (STD.ConsV v1 v2) = STD.ConsV8 (convertValue0To8 nv v1) (convertValue0To8 nv v2)

convertExpr0To8 :: Map String STD.Value8 -> STD.Expr -> STD.Expr8
convertExpr0To8 nv (STD.Var nm) = STD.Lit8 (nv ! nm)
convertExpr0To8 nv (STD.App e1 e2) = STD.App8 (convertExpr0To8 nv e1) (convertExpr0To8 nv e2)
convertExpr0To8 nv (STD.Let nm e1 e2) = STD.Let8 (convertExpr0To8 nv e1) (\v -> convertExpr0To8 (insert nm v nv) e2)
convertExpr0To8 nv (STD.OpCall nm e) = STD.OpCall8 nm (convertExpr0To8 nv e)
convertExpr0To8 nv (STD.Handle h e) = STD.Handle8 (convertHandler0To8 nv h) (convertExpr0To8 nv e)
convertExpr0To8 nv (STD.Lit v) = STD.Lit8 (convertValue0To8 nv v)
convertExpr0To8 nv (STD.Closed v) = STD.Lit8 (convertValue0To8 nv v)
convertExpr0To8 nv (STD.Pair e1 e2) = STD.Pair8 (convertExpr0To8 nv e1) (convertExpr0To8 nv e2)
convertExpr0To8 nv (STD.Cons e1 e2) = STD.Cons8 (convertExpr0To8 nv e1) (convertExpr0To8 nv e2)
convertExpr0To8 nv (STD.UnOp uop e) = STD.UnOp8 uop (convertExpr0To8 nv e)
convertExpr0To8 nv (STD.BinOp e1 bop e2) = STD.BinOp8 (convertExpr0To8 nv e1) bop (convertExpr0To8 nv e2)
convertExpr0To8 nv (STD.If e1 e2 e3) = STD.If8 (convertExpr0To8 nv e1) (convertExpr0To8 nv e2) (convertExpr0To8 nv e3)

---------------------------------------------------------------
---- Conversion from the STD.Result (0) to STD.Result9
---------------------------------------------------------------
convertResult0To9 :: STD.Result -> STD.Result9
convertResult0To9 (STD.Result v) = STD.NoOp9 (convertValue0To9 empty v)

---------------------------------------------------------------
---- Conversion from the STD.Expr0 to STD.Expr9
---------------------------------------------------------------
convertHandler0To9 :: Map String STD.Value9 -> STD.Handler -> STD.Handler9
convertHandler0To9 nv (STD.Handler ops (STD.ReturnI nmRet eRet)) =
  STD.Handler9
    ( ( \(STD.OpI opNm nmOpArg nmResume e) ->
          STD.OpI9 opNm (\vArg res' -> convertExpr0To9 (insert nmOpArg vArg $ insert nmResume (STD.LambdaV9 res') nv) e)
      )
        <$> ops
    )
    (\v -> convertExpr0To9 (insert nmRet v nv) eRet)

convertValue0To9 :: Map String STD.Value9 -> STD.Value -> STD.Value9
convertValue0To9 nv (STD.LambdaV nm e) = STD.LambdaV9 (\v -> convertExpr0To9 (insert nm v nv) e)
convertValue0To9 _ (STD.IntV i) = STD.IntV9 i
convertValue0To9 _ STD.UnitV = STD.UnitV9
convertValue0To9 _ (STD.BoolV b) = STD.BoolV9 b
convertValue0To9 nv (STD.PairV v1 v2) = STD.PairV9 (convertValue0To9 nv v1) (convertValue0To9 nv v2)
convertValue0To9 _ STD.NilV = STD.NilV9
convertValue0To9 nv (STD.ConsV v1 v2) = STD.ConsV9 (convertValue0To9 nv v1) (convertValue0To9 nv v2)

convertExpr0To9 :: Map String STD.Value9 -> STD.Expr -> STD.Expr9
convertExpr0To9 nv (STD.Var nm) = STD.Lit9 (nv ! nm)
convertExpr0To9 nv (STD.App e1 e2) = STD.app9 (convertExpr0To9 nv e1) (convertExpr0To9 nv e2)
convertExpr0To9 nv (STD.Let nm e1 e2) = STD.Let9 (convertExpr0To9 nv e1) (\v -> convertExpr0To9 (insert nm v nv) e2)
convertExpr0To9 nv (STD.OpCall nm e) = STD.op9 nm (convertExpr0To9 nv e)
convertExpr0To9 nv (STD.Handle h e) = STD.Handle9 (convertHandler0To9 nv h) (convertExpr0To9 nv e)
convertExpr0To9 nv (STD.Lit v) = STD.Lit9 (convertValue0To9 nv v)
convertExpr0To9 nv (STD.Closed v) = STD.Lit9 (convertValue0To9 nv v)
convertExpr0To9 nv (STD.Pair e1 e2) = STD.pair9 (convertExpr0To9 nv e1) (convertExpr0To9 nv e2)
convertExpr0To9 nv (STD.Cons e1 e2) = STD.cons9 (convertExpr0To9 nv e1) (convertExpr0To9 nv e2)
convertExpr0To9 nv (STD.UnOp uop e) = STD.unOp9 uop (convertExpr0To9 nv e)
convertExpr0To9 nv (STD.BinOp e1 bop e2) = STD.binOp9 (convertExpr0To9 nv e1) bop (convertExpr0To9 nv e2)
convertExpr0To9 nv (STD.If e1 e2 e3) = STD.if9 (convertExpr0To9 nv e1) (convertExpr0To9 nv e2) (convertExpr0To9 nv e3)

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr10
---------------------------------------------------------------
data C10 where
  C10 ::
    { c10Effs :: [TH.Dec],
      c10Where :: [TH.Dec],
      c10TIdx :: Int,
      c10RetIdx :: Int
    } ->
    C10

type R10 = StateT C10 IO

instance Quote R10 where
  newName = lift . newName

simpleBT :: (Quote m) => m TH.Type -> m TH.BangType
simpleBT = bangType (bang sourceNoUnpack noSourceStrictness)

appslT :: (Quote m) => m TH.Type -> [m TH.Type] -> m TH.Type
appslT = foldl appT

infixsrT :: (Quote m) => [m TH.Type] -> Name -> m TH.Type -> m TH.Type
infixsrT [] _ rgt = rgt
infixsrT (x : xs) ifx rgt = infixT x ifx (infixsrT xs ifx rgt)

infixslT :: (Quote m) => m TH.Type -> Name -> [m TH.Type] -> m TH.Type
infixslT lft _ [] = lft
infixslT lft ifx (x : xs) = infixslT (infixT lft ifx x) ifx xs

convertType0To10 :: (MonadState C10 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To10 t = appslT (conT $ mkName "Value10") [convertType0To10' t]

convertType0To10' :: (MonadState C10 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To10' (FunT argT retT) = appslT arrowT [convertType0To10' argT, convertEType0To10 retT]
convertType0To10' IntT = varT $ mkName "Int"
convertType0To10' BoolT = varT $ mkName "Bool"
convertType0To10' UnitT = varT $ mkName "()"
convertType0To10' (PairT t1 t2) = appslT (tupleT 2) [convertType0To10' t1, convertType0To10' t2]
convertType0To10' (PG.ListT t) = appslT listT [convertType0To10' t]
convertType0To10' (PG.VarT n) = varT $ mkName $ toTyVarName n

convertEType0To10 :: (MonadState C10 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To10 (EType effs t) = do
  tIdx <- gets c10TIdx
  appslT
    (conT (mkName "Expr10"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To10' t
    ]

convertEType0To10' :: (MonadState C10 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To10' (EType _ t) = do
  appslT
    (conT (mkName "Expr10"))
    [ varT $ mkName "sig",
      convertType0To10' t
    ]

convertHandler0To10 :: (MonadState C10 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To10 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c10TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To10 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To10' opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c10RetIdx)
  modify (\c10 -> c10 {c10RetIdx = c10RetIdx c10 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To10 argT, resT]) (appslT arrowT [convertType0To10 retArgType, convertEType0To10 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To10 eRet) []]

  modify (\c10 -> c10 {c10Effs = c10Effs c10 <> [dd], c10Where = c10Where c10 <> [retTD, retD]})

  appsE
    [ varE $ mkName "Handler10",
      lamE [varP $ mkName "opArg", varP $ mkName "resumeF"] $
        letE [valD (varP $ mkName "resume") (normalB $ appsE [conE $ mkName "LambdaV10", varE $ mkName "resumeF"]) []] $
          caseE (varE $ mkName "opArg") $
            ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
                match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To10 eOp) []
            )
              <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To10 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To10 Fst = varE $ mkName "Fst10"
convertUnOp0To10 Snd = varE $ mkName "Snd10"

convertBinOp0To10 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To10 Concat = varE $ mkName "Concat10"
convertBinOp0To10 Add = varE $ mkName "Add10"
convertBinOp0To10 Mul = varE $ mkName "Mul10"

convertResult10To0 :: STD.Result10 sig a -> STD.Result
convertResult10To0 (STD.NoOp10 v) = STD.Result $ convertValue10To0 v
convertResult10To0 (STD.Op10 _ _) = STD.Wrong "Invalid [10], an operation was left unhandled"

convertValue10To0 :: STD.Value10 a -> STD.Value
convertValue10To0 (STD.IntV10 v) = STD.IntV v
convertValue10To0 (STD.BoolV10 v) = STD.BoolV v
convertValue10To0 STD.NilV10 = STD.NilV
convertValue10To0 STD.UnitV10 = STD.UnitV
convertValue10To0 (STD.PairV10 v1 v2) = STD.PairV (convertValue10To0 v1) (convertValue10To0 v2)
convertValue10To0 (STD.ConsV10 v1 v2) = STD.ConsV (convertValue10To0 v1) (convertValue10To0 v2)

convertValue0To10 :: (MonadState C10 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To10 (LambdaV nm e) =
  appsE [varE $ mkName "LambdaV10", lamE [varP $ mkName $ toVarName nm] $ convertExpr0To10 e]
convertValue0To10 (IntV i) =
  appsE [varE $ mkName "IntV10", litE $ integerL $ toInteger i]
convertValue0To10 UnitV = varE $ mkName "UnitV10"
convertValue0To10 (BoolV b) =
  appsE [varE $ mkName "BoolV10", varE $ mkName $ show b]
convertValue0To10 (PairV v1 v2) =
  appsE [varE $ mkName "PairV10", convertValue0To10 v1, convertValue0To10 v2]
convertValue0To10 NilV =
  varE $ mkName "NilV10"
convertValue0To10 (ConsV v1 v2) =
  appsE [varE $ mkName "ConsV10", convertValue0To10 v1, convertValue0To10 v2]

convertExpr0To10 :: (MonadState C10 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To10 (Var varIdx) =
  appsE [conE $ mkName "Lit10", varE $ mkName $ toVarName varIdx]
convertExpr0To10 (App e1 e2) =
  appsE [varE $ mkName "app10", convertExpr0To10 e1, convertExpr0To10 e2]
convertExpr0To10 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let10", convertExpr0To10 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To10 e2]
convertExpr0To10 (OpCall effIdx opIdx e) = do
  tIdx <- gets c10TIdx
  appsE [varE $ mkName "op10", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To10 e]
convertExpr0To10 (Handle h e) =
  appsE [conE $ mkName "Handle10", convertHandler0To10 h, convertExpr0To10 e]
convertExpr0To10 (Lit v) =
  appsE [conE $ mkName "Lit10", convertValue0To10 v]
convertExpr0To10 (Pair e1 e2) =
  appsE [varE $ mkName "pair10", convertExpr0To10 e1, convertExpr0To10 e2]
convertExpr0To10 (Cons e1 e2) =
  appsE [varE $ mkName "cons10", convertExpr0To10 e1, convertExpr0To10 e2]
convertExpr0To10 (UnOp uop e) =
  appsE [varE $ mkName "unOp10", convertUnOp0To10 uop, convertExpr0To10 e]
convertExpr0To10 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp10", convertExpr0To10 e1, convertBinOp0To10 bop, convertExpr0To10 e2]
convertExpr0To10 (If e1 e2 e3) =
  appsE [varE $ mkName "if10", convertExpr0To10 e1, convertExpr0To10 e2, convertExpr0To10 e3]
convertExpr0To10 (Resume e) =
  appsE [varE $ mkName "app10", appsE [conE $ mkName "Lit10", varE $ mkName "resume"], convertExpr0To10 e]

newtype P10
  = P10 TH.Exp
  deriving (Show)

instance Ppr P10 where
  ppr (P10 e) = ppr e

testFile10 :: FilePath
testFile10 = "test-generated/Final/SmallToDeepTests10.hs"

testModule10 :: String
testModule10 = "Final.SmallToDeepTests10"

createTestString10 :: Int -> PG.Type -> Expr -> IO String
createTestString10 testIdx ty e =
  flip evalStateT (C10 [] [] testIdx 0) $ do
    e10 <- convertExpr0To10 e

    effs <- gets c10Effs
    decs <- gets c10Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "Result")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE [varE $ mkName "convertResult10To0", appsE [varE $ mkName "eval10", return e10]]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter10 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter10 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString10 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile10
    when fExists (removeFile testFile10)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile10
      ( "module "
          <> testModule10
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.SmallToDeep"
          <> "\n"
          <> "import Final.SmallToDeepTest (convertResult10To0)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the evaler by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.SmallToDeep", "Final.SmallToDeepTest", testModule10]
  setImports ["Final.SmallToDeep", testModule10]

  -- Run the many tests in this test set by using many 'eval' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v0 = STD.normalise0 $ convertToExpr0 e
        v10 <- interpret ("p" <> show testIdx) (as :: STD.Result)
        return (liftBool (v0 == v10))
    )
    tes
    [1 ..]

testMany10 :: Int -> Property
testMany10 n = ioProperty $ do
  results <- runInterpreter tests
  case results of
    Left err -> return (property (exception (displayException err) (throw err)))
    Right props -> return $ conjoin $ concat props
  where
    (nBatches, leftover) = n `divMod` maxBatchSize
    batchSizes = replicate nBatches maxBatchSize <> [leftover | leftover > 0]
    tests =
      traverse
        ( \sz -> do
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndDeepExpr
            testBatchInterpreter10 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr11
---------------------------------------------------------------
data C11 where
  C11 ::
    { c11Effs :: [TH.Dec],
      c11Where :: [TH.Dec],
      c11TIdx :: Int,
      c11RetIdx :: Int
    } ->
    C11

type R11 = StateT C11 IO

instance Quote R11 where
  newName = lift . newName

convertType0To11 :: (MonadState C11 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To11 (FunT argT retT) = appslT arrowT [convertType0To11 argT, convertEType0To11 retT]
convertType0To11 IntT = varT $ mkName "Int"
convertType0To11 BoolT = varT $ mkName "Bool"
convertType0To11 UnitT = varT $ mkName "()"
convertType0To11 (PairT t1 t2) = appslT (tupleT 2) [convertType0To11 t1, convertType0To11 t2]
convertType0To11 (PG.ListT t) = appslT listT [convertType0To11 t]
convertType0To11 (PG.VarT n) = varT $ mkName $ toTyVarName n

convertEType0To11 :: (MonadState C11 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To11 (EType effs t) = do
  tIdx <- gets c11TIdx
  appslT
    (conT (mkName "Expr11"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To11 t
    ]

convertEType0To11' :: (MonadState C11 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To11' (EType _ t) = do
  appslT
    (conT (mkName "Expr11"))
    [ varT $ mkName "sig",
      convertType0To11 t
    ]

convertHandler0To11 :: (MonadState C11 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To11 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c11TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To11 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To11 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c11RetIdx)
  modify (\c11 -> c11 {c11RetIdx = c11RetIdx c11 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To11 argT, resT]) (appslT arrowT [convertType0To11 retArgType, convertEType0To11 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To11 eRet) []]

  modify (\c11 -> c11 {c11Effs = c11Effs c11 <> [dd], c11Where = c11Where c11 <> [retTD, retD]})

  appsE
    [ varE $ mkName "Handler11",
      lamE [varP $ mkName "opArg", varP $ mkName "resume"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To11 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To11 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To11 Fst = varE $ mkName "fst"
convertUnOp0To11 Snd = varE $ mkName "snd"

convertBinOp0To11 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To11 Concat = varE $ mkName "(++)"
convertBinOp0To11 Add = varE $ mkName "(+)"
convertBinOp0To11 Mul = varE $ mkName "(*)"

convertResult11To0 :: STD.Result11 sig a -> (a -> STD.Value) -> STD.Result
convertResult11To0 (STD.NoOp11 v) convert = STD.Result $ convert v
convertResult11To0 (STD.Op11 _ _) _ = STD.Wrong "Invalid [11], an operation was left unhandled"

convertValue11To0Int :: Int -> STD.Value
convertValue11To0Int = STD.IntV

convertValue11To0Bool :: Bool -> STD.Value
convertValue11To0Bool = STD.BoolV

convertValue11To0Unit :: () -> STD.Value
convertValue11To0Unit _ = STD.UnitV

convertValue11To0List :: (a -> STD.Value) -> [a] -> STD.Value
convertValue11To0List _ [] = STD.NilV
convertValue11To0List fa (a : as) = STD.ConsV (fa a) (convertValue11To0List fa as)

convertValue11To0Pair :: (a -> STD.Value) -> (b -> STD.Value) -> (a, b) -> STD.Value
convertValue11To0Pair fa fb (a, b) = STD.PairV (fa a) (fb b)

createValueConversionFunction11 :: (MonadState C11 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction11 IntT = varE $ mkName "convertValue11To0Int"
createValueConversionFunction11 BoolT = varE $ mkName "convertValue11To0Bool"
createValueConversionFunction11 UnitT = varE $ mkName "convertValue11To0Unit"
createValueConversionFunction11 (PairT t1 t2) = appsE [varE $ mkName "convertValue11To0Pair", createValueConversionFunction11 t1, createValueConversionFunction11 t2]
createValueConversionFunction11 (PG.ListT t) = appsE [varE $ mkName "convertValue11To0List", createValueConversionFunction11 t]

convertValue0To11 :: (MonadState C11 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To11 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To11 e
convertValue0To11 (IntV i) = litE $ integerL $ toInteger i
convertValue0To11 UnitV = conE $ mkName "()"
convertValue0To11 (BoolV b) = varE $ mkName $ show b
convertValue0To11 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To11 v1, convertValue0To11 v2]
convertValue0To11 NilV = conE $ mkName "[]"
convertValue0To11 (ConsV v1 v2) = infixE (Just $ convertValue0To11 v1) (varE $ mkName ":") (Just $ convertValue0To11 v2)

convertExpr0To11 :: (MonadState C11 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To11 (Var varIdx) =
  appsE [conE $ mkName "Lit11", varE $ mkName $ toVarName varIdx]
convertExpr0To11 (App e1 e2) =
  appsE [varE $ mkName "app11", convertExpr0To11 e1, convertExpr0To11 e2]
convertExpr0To11 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let11", convertExpr0To11 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To11 e2]
convertExpr0To11 (OpCall effIdx opIdx e) = do
  tIdx <- gets c11TIdx
  appsE [varE $ mkName "op11", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To11 e]
convertExpr0To11 (Handle h e) =
  appsE [conE $ mkName "Handle11", convertHandler0To11 h, convertExpr0To11 e]
convertExpr0To11 (Lit v) =
  appsE [conE $ mkName "Lit11", convertValue0To11 v]
convertExpr0To11 (Pair e1 e2) =
  appsE [varE $ mkName "pair11", convertExpr0To11 e1, convertExpr0To11 e2]
convertExpr0To11 (Cons e1 e2) =
  appsE [varE $ mkName "cons11", convertExpr0To11 e1, convertExpr0To11 e2]
convertExpr0To11 (UnOp uop e) =
  appsE [varE $ mkName "unOp11", convertUnOp0To11 uop, convertExpr0To11 e]
convertExpr0To11 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp11", convertExpr0To11 e1, convertBinOp0To11 bop, convertExpr0To11 e2]
convertExpr0To11 (If e1 e2 e3) =
  appsE [varE $ mkName "if11", convertExpr0To11 e1, convertExpr0To11 e2, convertExpr0To11 e3]
convertExpr0To11 (Resume e) =
  appsE [varE $ mkName "app11", appsE [conE $ mkName "Lit11", varE $ mkName "resume"], convertExpr0To11 e]

newtype P11
  = P11 TH.Exp
  deriving (Show)

instance Ppr P11 where
  ppr (P11 e) = ppr e

testFile11 :: FilePath
testFile11 = "test-generated/Final/SmallToDeepTests11.hs"

testModule11 :: String
testModule11 = "Final.SmallToDeepTests11"

createTestString11 :: Int -> PG.Type -> Expr -> IO String
createTestString11 testIdx ty e =
  flip evalStateT (C11 [] [] testIdx 0) $ do
    e11 <- convertExpr0To11 e

    effs <- gets c11Effs
    decs <- gets c11Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "Result")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "convertResult11To0",
                appsE [varE $ mkName "eval11", return e11],
                createValueConversionFunction11 ty
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter11 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter11 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString11 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile11
    when fExists (removeFile testFile11)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile11
      ( "module "
          <> testModule11
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.SmallToDeep"
          <> "\n"
          <> "import Final.SmallToDeepTest (convertResult11To0, convertValue11To0Int, convertValue11To0List, convertValue11To0Pair, convertValue11To0Bool, convertValue11To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the evaler by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.SmallToDeep", "Final.SmallToDeepTest", testModule11]
  setImports ["Final.SmallToDeep", testModule11]

  -- Run the many tests in this test set by using many 'eval' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v0 = STD.normalise0 $ convertToExpr0 e
        v11 <- interpret ("p" <> show testIdx) (as :: STD.Result)
        return (liftBool (v0 == v11))
    )
    tes
    [1 ..]

testMany11 :: Int -> Property
testMany11 n = ioProperty $ do
  results <- runInterpreter tests
  case results of
    Left err -> return (property (exception (displayException err) (throw err)))
    Right props -> return $ conjoin $ concat props
  where
    (nBatches, leftover) = n `divMod` maxBatchSize
    batchSizes = replicate nBatches maxBatchSize <> [leftover | leftover > 0]
    tests =
      traverse
        ( \sz -> do
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndDeepExpr
            testBatchInterpreter11 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr12
---------------------------------------------------------------
data C12 where
  C12 ::
    { c12Effs :: [TH.Dec],
      c12Where :: [TH.Dec],
      c12TIdx :: Int,
      c12RetIdx :: Int
    } ->
    C12

type R12 = StateT C12 IO

instance Quote R12 where
  newName = lift . newName

convertType0To12 :: (MonadState C12 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To12 (FunT argT retT) = appslT arrowT [convertType0To12 argT, convertEType0To12 retT]
convertType0To12 IntT = varT $ mkName "Int"
convertType0To12 BoolT = varT $ mkName "Bool"
convertType0To12 UnitT = varT $ mkName "()"
convertType0To12 (PairT t1 t2) = appslT (tupleT 2) [convertType0To12 t1, convertType0To12 t2]
convertType0To12 (PG.ListT t) = appslT listT [convertType0To12 t]
convertType0To12 (PG.VarT n) = varT $ mkName $ toTyVarName n

convertEType0To12 :: (MonadState C12 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To12 (EType effs t) = do
  tIdx <- gets c12TIdx
  appslT
    (conT (mkName "Expr12"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To12 t
    ]

convertEType0To12' :: (MonadState C12 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To12' (EType _ t) = do
  appslT
    (conT (mkName "Expr12"))
    [ varT $ mkName "sig",
      convertType0To12 t
    ]

convertHandler0To12 :: (MonadState C12 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To12 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c12TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To12 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To12 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c12RetIdx)
  modify (\c12 -> c12 {c12RetIdx = c12RetIdx c12 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To12 argT, resT]) (appslT arrowT [convertType0To12 retArgType, convertEType0To12 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To12 eRet) []]

  modify (\c12 -> c12 {c12Effs = c12Effs c12 <> [dd], c12Where = c12Where c12 <> [retTD, retD]})

  appsE
    [ varE $ mkName "Handler12",
      lamE [varP $ mkName "opArg", varP $ mkName "resume"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To12 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To12 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To12 Fst = varE $ mkName "fst"
convertUnOp0To12 Snd = varE $ mkName "snd"

convertBinOp0To12 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To12 Concat = varE $ mkName "(++)"
convertBinOp0To12 Add = varE $ mkName "(+)"
convertBinOp0To12 Mul = varE $ mkName "(*)"

convertResult12To0 :: STD.Result12 sig a -> (a -> STD.Value) -> STD.Result
convertResult12To0 (STD.NoOp12 v) convert = STD.Result $ convert v
convertResult12To0 (STD.Op12 _ _) _ = STD.Wrong "Invalid [12], an operation was left unhandled"

convertValue12To0Int :: Int -> STD.Value
convertValue12To0Int = STD.IntV

convertValue12To0Bool :: Bool -> STD.Value
convertValue12To0Bool = STD.BoolV

convertValue12To0Unit :: () -> STD.Value
convertValue12To0Unit _ = STD.UnitV

convertValue12To0List :: (a -> STD.Value) -> [a] -> STD.Value
convertValue12To0List _ [] = STD.NilV
convertValue12To0List fa (a : as) = STD.ConsV (fa a) (convertValue12To0List fa as)

convertValue12To0Pair :: (a -> STD.Value) -> (b -> STD.Value) -> (a, b) -> STD.Value
convertValue12To0Pair fa fb (a, b) = STD.PairV (fa a) (fb b)

createValueConversionFunction12 :: (MonadState C12 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction12 IntT = varE $ mkName "convertValue12To0Int"
createValueConversionFunction12 BoolT = varE $ mkName "convertValue12To0Bool"
createValueConversionFunction12 UnitT = varE $ mkName "convertValue12To0Unit"
createValueConversionFunction12 (PairT t1 t2) = appsE [varE $ mkName "convertValue12To0Pair", createValueConversionFunction12 t1, createValueConversionFunction12 t2]
createValueConversionFunction12 (PG.ListT t) = appsE [varE $ mkName "convertValue12To0List", createValueConversionFunction12 t]

convertValue0To12 :: (MonadState C12 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To12 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To12 e
convertValue0To12 (IntV i) = litE $ integerL $ toInteger i
convertValue0To12 UnitV = conE $ mkName "()"
convertValue0To12 (BoolV b) = varE $ mkName $ show b
convertValue0To12 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To12 v1, convertValue0To12 v2]
convertValue0To12 NilV = conE $ mkName "[]"
convertValue0To12 (ConsV v1 v2) = infixE (Just $ convertValue0To12 v1) (varE $ mkName ":") (Just $ convertValue0To12 v2)

convertExpr0To12 :: (MonadState C12 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To12 (Var varIdx) =
  appsE [conE $ mkName "Lit12", varE $ mkName $ toVarName varIdx]
convertExpr0To12 (App e1 e2) =
  appsE [varE $ mkName "app12", convertExpr0To12 e1, convertExpr0To12 e2]
convertExpr0To12 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let12", convertExpr0To12 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To12 e2]
convertExpr0To12 (OpCall effIdx opIdx e) = do
  tIdx <- gets c12TIdx
  appsE [varE $ mkName "op12", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To12 e]
convertExpr0To12 (Handle h e) =
  appsE [conE $ mkName "handle12", convertHandler0To12 h, convertExpr0To12 e]
convertExpr0To12 (Lit v) =
  appsE [conE $ mkName "Lit12", convertValue0To12 v]
convertExpr0To12 (Pair e1 e2) =
  appsE [varE $ mkName "pair12", convertExpr0To12 e1, convertExpr0To12 e2]
convertExpr0To12 (Cons e1 e2) =
  appsE [varE $ mkName "cons12", convertExpr0To12 e1, convertExpr0To12 e2]
convertExpr0To12 (UnOp uop e) =
  appsE [varE $ mkName "unOp12", convertUnOp0To12 uop, convertExpr0To12 e]
convertExpr0To12 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp12", convertExpr0To12 e1, convertBinOp0To12 bop, convertExpr0To12 e2]
convertExpr0To12 (If e1 e2 e3) =
  appsE [varE $ mkName "if12", convertExpr0To12 e1, convertExpr0To12 e2, convertExpr0To12 e3]
convertExpr0To12 (Resume e) =
  appsE [varE $ mkName "app12", appsE [conE $ mkName "Lit12", varE $ mkName "resume"], convertExpr0To12 e]

newtype P12
  = P12 TH.Exp
  deriving (Show)

instance Ppr P12 where
  ppr (P12 e) = ppr e

testFile12 :: FilePath
testFile12 = "test-generated/Final/SmallToDeepTests12.hs"

testModule12 :: String
testModule12 = "Final.SmallToDeepTests12"

createTestString12 :: Int -> PG.Type -> Expr -> IO String
createTestString12 testIdx ty e =
  flip evalStateT (C12 [] [] testIdx 0) $ do
    e12 <- convertExpr0To12 e

    effs <- gets c12Effs
    decs <- gets c12Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "Result")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "convertResult12To0",
                appsE [varE $ mkName "eval12", return e12],
                createValueConversionFunction12 ty
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter12 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter12 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString12 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile12
    when fExists (removeFile testFile12)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile12
      ( "module "
          <> testModule12
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.SmallToDeep"
          <> "\n"
          <> "import Final.SmallToDeepTest (convertResult12To0, convertValue12To0Int, convertValue12To0List, convertValue12To0Pair, convertValue12To0Bool, convertValue12To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the evaler by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.SmallToDeep", "Final.SmallToDeepTest", testModule12]
  setImports ["Final.SmallToDeep", testModule12]

  -- Run the many tests in this test set by using many 'eval' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v0 = STD.normalise0 $ convertToExpr0 e
        v12 <- interpret ("p" <> show testIdx) (as :: STD.Result)
        return (liftBool (v0 == v12))
    )
    tes
    [1 ..]

testMany12 :: Int -> Property
testMany12 n = ioProperty $ do
  results <- runInterpreter tests
  case results of
    Left err -> return (property (exception (displayException err) (throw err)))
    Right props -> return $ conjoin $ concat props
  where
    (nBatches, leftover) = n `divMod` maxBatchSize
    batchSizes = replicate nBatches maxBatchSize <> [leftover | leftover > 0]
    tests =
      traverse
        ( \sz -> do
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndDeepExpr
            testBatchInterpreter12 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr13
---------------------------------------------------------------
data C13 where
  C13 ::
    { c13Effs :: [TH.Dec],
      c13Where :: [TH.Dec],
      c13TIdx :: Int,
      c13RetIdx :: Int
    } ->
    C13

type R13 = StateT C13 IO

instance Quote R13 where
  newName = lift . newName

convertType0To13 :: (MonadState C13 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To13 (FunT argT retT) = appslT arrowT [convertType0To13 argT, convertEType0To13 retT]
convertType0To13 IntT = varT $ mkName "Int"
convertType0To13 BoolT = varT $ mkName "Bool"
convertType0To13 UnitT = varT $ mkName "()"
convertType0To13 (PairT t1 t2) = appslT (tupleT 2) [convertType0To13 t1, convertType0To13 t2]
convertType0To13 (PG.ListT t) = appslT listT [convertType0To13 t]
convertType0To13 (PG.VarT n) = varT $ mkName $ toTyVarName n

convertEType0To13 :: (MonadState C13 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To13 (EType effs t) = do
  tIdx <- gets c13TIdx
  appslT
    (conT (mkName "Expr13"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To13 t
    ]

convertEType0To13' :: (MonadState C13 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To13' (EType _ t) = do
  appslT
    (conT (mkName "Expr13"))
    [ varT $ mkName "sig",
      convertType0To13 t
    ]

convertHandler0To13 :: (MonadState C13 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To13 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c13TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To13 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To13 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c13RetIdx)
  modify (\c13 -> c13 {c13RetIdx = c13RetIdx c13 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To13 argT, resT]) (appslT arrowT [convertType0To13 retArgType, convertEType0To13 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To13 eRet) []]

  modify (\c13 -> c13 {c13Effs = c13Effs c13 <> [dd], c13Where = c13Where c13 <> [retTD, retD]})

  appsE
    [ varE $ mkName "Handler13",
      lamE [varP $ mkName "opArg", varP $ mkName "resume"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To13 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To13 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To13 Fst = varE $ mkName "fst"
convertUnOp0To13 Snd = varE $ mkName "snd"

convertBinOp0To13 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To13 Concat = varE $ mkName "(++)"
convertBinOp0To13 Add = varE $ mkName "(+)"
convertBinOp0To13 Mul = varE $ mkName "(*)"

convertResult13To0 :: STD.Result13 sig a -> (a -> STD.Value) -> STD.Result
convertResult13To0 (STD.NoOp13 v) convert = STD.Result $ convert v
convertResult13To0 (STD.Op13 _ _) _ = STD.Wrong "Invalid [13], an operation was left unhandled"

convertValue13To0Int :: Int -> STD.Value
convertValue13To0Int = STD.IntV

convertValue13To0Bool :: Bool -> STD.Value
convertValue13To0Bool = STD.BoolV

convertValue13To0Unit :: () -> STD.Value
convertValue13To0Unit _ = STD.UnitV

convertValue13To0List :: (a -> STD.Value) -> [a] -> STD.Value
convertValue13To0List _ [] = STD.NilV
convertValue13To0List fa (a : as) = STD.ConsV (fa a) (convertValue13To0List fa as)

convertValue13To0Pair :: (a -> STD.Value) -> (b -> STD.Value) -> (a, b) -> STD.Value
convertValue13To0Pair fa fb (a, b) = STD.PairV (fa a) (fb b)

createValueConversionFunction13 :: (MonadState C13 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction13 IntT = varE $ mkName "convertValue13To0Int"
createValueConversionFunction13 BoolT = varE $ mkName "convertValue13To0Bool"
createValueConversionFunction13 UnitT = varE $ mkName "convertValue13To0Unit"
createValueConversionFunction13 (PairT t1 t2) = appsE [varE $ mkName "convertValue13To0Pair", createValueConversionFunction13 t1, createValueConversionFunction13 t2]
createValueConversionFunction13 (PG.ListT t) = appsE [varE $ mkName "convertValue13To0List", createValueConversionFunction13 t]

convertValue0To13 :: (MonadState C13 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To13 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To13 e
convertValue0To13 (IntV i) = litE $ integerL $ toInteger i
convertValue0To13 UnitV = conE $ mkName "()"
convertValue0To13 (BoolV b) = varE $ mkName $ show b
convertValue0To13 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To13 v1, convertValue0To13 v2]
convertValue0To13 NilV = conE $ mkName "[]"
convertValue0To13 (ConsV v1 v2) = infixE (Just $ convertValue0To13 v1) (varE $ mkName ":") (Just $ convertValue0To13 v2)

convertExpr0To13 :: (MonadState C13 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To13 (Var varIdx) =
  appsE [conE $ mkName "Lit13", varE $ mkName $ toVarName varIdx]
convertExpr0To13 (App e1 e2) =
  appsE [varE $ mkName "app13", convertExpr0To13 e1, convertExpr0To13 e2]
convertExpr0To13 (Let argIdx e1 e2) =
  appsE [conE $ mkName "let13", convertExpr0To13 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To13 e2]
convertExpr0To13 (OpCall effIdx opIdx e) = do
  tIdx <- gets c13TIdx
  appsE [varE $ mkName "op13", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To13 e]
convertExpr0To13 (Handle h e) =
  appsE [conE $ mkName "handle13", convertHandler0To13 h, convertExpr0To13 e]
convertExpr0To13 (Lit v) =
  appsE [conE $ mkName "Lit13", convertValue0To13 v]
convertExpr0To13 (Pair e1 e2) =
  appsE [varE $ mkName "pair13", convertExpr0To13 e1, convertExpr0To13 e2]
convertExpr0To13 (Cons e1 e2) =
  appsE [varE $ mkName "cons13", convertExpr0To13 e1, convertExpr0To13 e2]
convertExpr0To13 (UnOp uop e) =
  appsE [varE $ mkName "unOp13", convertUnOp0To13 uop, convertExpr0To13 e]
convertExpr0To13 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp13", convertExpr0To13 e1, convertBinOp0To13 bop, convertExpr0To13 e2]
convertExpr0To13 (If e1 e2 e3) =
  appsE [varE $ mkName "if13", convertExpr0To13 e1, convertExpr0To13 e2, convertExpr0To13 e3]
convertExpr0To13 (Resume e) =
  appsE [varE $ mkName "app13", appsE [conE $ mkName "Lit13", varE $ mkName "resume"], convertExpr0To13 e]

newtype P13
  = P13 TH.Exp
  deriving (Show)

instance Ppr P13 where
  ppr (P13 e) = ppr e

testFile13 :: FilePath
testFile13 = "test-generated/Final/SmallToDeepTests13.hs"

testModule13 :: String
testModule13 = "Final.SmallToDeepTests13"

createTestString13 :: Int -> PG.Type -> Expr -> IO String
createTestString13 testIdx ty e =
  flip evalStateT (C13 [] [] testIdx 0) $ do
    e13 <- convertExpr0To13 e

    effs <- gets c13Effs
    decs <- gets c13Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "Result")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "convertResult13To0",
                appsE [varE $ mkName "eval13", return e13],
                createValueConversionFunction13 ty
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter13 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter13 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString13 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile13
    when fExists (removeFile testFile13)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile13
      ( "module "
          <> testModule13
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.SmallToDeep"
          <> "\n"
          <> "import Final.SmallToDeepTest (convertResult13To0, convertValue13To0Int, convertValue13To0List, convertValue13To0Pair, convertValue13To0Bool, convertValue13To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the evaler by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.SmallToDeep", "Final.SmallToDeepTest", testModule13]
  setImports ["Final.SmallToDeep", testModule13]

  -- Run the many tests in this test set by using many 'eval' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v0 = STD.normalise0 $ convertToExpr0 e
        v13 <- interpret ("p" <> show testIdx) (as :: STD.Result)
        return (liftBool (v0 == v13))
    )
    tes
    [1 ..]

testMany13 :: Int -> Property
testMany13 n = ioProperty $ do
  results <- runInterpreter tests
  case results of
    Left err -> return (property (exception (displayException err) (throw err)))
    Right props -> return $ conjoin $ concat props
  where
    (nBatches, leftover) = n `divMod` maxBatchSize
    batchSizes = replicate nBatches maxBatchSize <> [leftover | leftover > 0]
    tests =
      traverse
        ( \sz -> do
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndDeepExpr
            testBatchInterpreter13 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Freer
---------------------------------------------------------------
data C14 where
  C14 ::
    { c14Effs :: [TH.Dec],
      c14Where :: [TH.Dec],
      c14TIdx :: Int,
      c14RetIdx :: Int
    } ->
    C14

type R14 = StateT C14 IO

instance Quote R14 where
  newName = lift . newName

convertType0To14 :: (MonadState C14 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To14 (FunT argT retT) = appslT arrowT [convertType0To14 argT, convertEType0To14 retT]
convertType0To14 IntT = varT $ mkName "Int"
convertType0To14 BoolT = varT $ mkName "Bool"
convertType0To14 UnitT = varT $ mkName "()"
convertType0To14 (PairT t1 t2) = appslT (tupleT 2) [convertType0To14 t1, convertType0To14 t2]
convertType0To14 (PG.ListT t) = appslT listT [convertType0To14 t]
convertType0To14 (PG.VarT n) = varT $ mkName $ toTyVarName n

convertEType0To14 :: (MonadState C14 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To14 (EType effs t) = do
  tIdx <- gets c14TIdx
  appslT
    (conT (mkName "Freer"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To14 t
    ]

convertEType0To14' :: (MonadState C14 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To14' (EType _ t) = do
  appslT
    (conT (mkName "Freer"))
    [ varT $ mkName "sig",
      convertType0To14 t
    ]

convertHandler0To14 :: (MonadState C14 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To14 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c14TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To14 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To14 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c14RetIdx)
  modify (\c14 -> c14 {c14RetIdx = c14RetIdx c14 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To14 argT, resT]) (appslT arrowT [convertType0To14 retArgType, convertEType0To14 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To14 eRet) []]

  modify (\c14 -> c14 {c14Effs = c14Effs c14 <> [dd], c14Where = c14Where c14 <> [retTD, retD]})

  appsE
    [ varE $ mkName "Handler14",
      lamE [varP $ mkName "opArg", varP $ mkName "resume"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To14 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To14 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To14 Fst = varE $ mkName "fst"
convertUnOp0To14 Snd = varE $ mkName "snd"

convertBinOp0To14 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To14 Concat = varE $ mkName "(++)"
convertBinOp0To14 Add = varE $ mkName "(+)"
convertBinOp0To14 Mul = varE $ mkName "(*)"

convertResult14To0 :: STD.Result14 sig a -> (a -> STD.Value) -> STD.Result
convertResult14To0 (STD.NoOp14 v) convert = STD.Result $ convert v
convertResult14To0 (STD.Op14 _ _) _ = STD.Wrong "Invalid [14], an operation was left unhandled"

convertValue14To0Int :: Int -> STD.Value
convertValue14To0Int = STD.IntV

convertValue14To0Bool :: Bool -> STD.Value
convertValue14To0Bool = STD.BoolV

convertValue14To0Unit :: () -> STD.Value
convertValue14To0Unit _ = STD.UnitV

convertValue14To0List :: (a -> STD.Value) -> [a] -> STD.Value
convertValue14To0List _ [] = STD.NilV
convertValue14To0List fa (a : as) = STD.ConsV (fa a) (convertValue14To0List fa as)

convertValue14To0Pair :: (a -> STD.Value) -> (b -> STD.Value) -> (a, b) -> STD.Value
convertValue14To0Pair fa fb (a, b) = STD.PairV (fa a) (fb b)

createValueConversionFunction14 :: (MonadState C14 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction14 IntT = varE $ mkName "convertValue14To0Int"
createValueConversionFunction14 BoolT = varE $ mkName "convertValue14To0Bool"
createValueConversionFunction14 UnitT = varE $ mkName "convertValue14To0Unit"
createValueConversionFunction14 (PairT t1 t2) = appsE [varE $ mkName "convertValue14To0Pair", createValueConversionFunction14 t1, createValueConversionFunction14 t2]
createValueConversionFunction14 (PG.ListT t) = appsE [varE $ mkName "convertValue14To0List", createValueConversionFunction14 t]

convertValue0To14 :: (MonadState C14 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To14 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To14 e
convertValue0To14 (IntV i) = litE $ integerL $ toInteger i
convertValue0To14 UnitV = conE $ mkName "()"
convertValue0To14 (BoolV b) = varE $ mkName $ show b
convertValue0To14 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To14 v1, convertValue0To14 v2]
convertValue0To14 NilV = conE $ mkName "[]"
convertValue0To14 (ConsV v1 v2) = infixE (Just $ convertValue0To14 v1) (varE $ mkName ":") (Just $ convertValue0To14 v2)

convertExpr0To14 :: (MonadState C14 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To14 (Var varIdx) =
  appsE [conE $ mkName "Pure", varE $ mkName $ toVarName varIdx]
convertExpr0To14 (App e1 e2) =
  appsE [varE $ mkName "app14", convertExpr0To14 e1, convertExpr0To14 e2]
convertExpr0To14 (Let argIdx e1 e2) =
  appsE [conE $ mkName "let14", convertExpr0To14 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To14 e2]
convertExpr0To14 (OpCall effIdx opIdx e) = do
  tIdx <- gets c14TIdx
  appsE [varE $ mkName "op14", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To14 e]
convertExpr0To14 (Handle h e) =
  appsE [conE $ mkName "handle14", convertHandler0To14 h, convertExpr0To14 e]
convertExpr0To14 (Lit v) =
  appsE [conE $ mkName "Pure", convertValue0To14 v]
convertExpr0To14 (Pair e1 e2) =
  appsE [varE $ mkName "pair14", convertExpr0To14 e1, convertExpr0To14 e2]
convertExpr0To14 (Cons e1 e2) =
  appsE [varE $ mkName "cons14", convertExpr0To14 e1, convertExpr0To14 e2]
convertExpr0To14 (UnOp uop e) =
  appsE [varE $ mkName "unOp14", convertUnOp0To14 uop, convertExpr0To14 e]
convertExpr0To14 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp14", convertExpr0To14 e1, convertBinOp0To14 bop, convertExpr0To14 e2]
convertExpr0To14 (If e1 e2 e3) =
  appsE [varE $ mkName "if14", convertExpr0To14 e1, convertExpr0To14 e2, convertExpr0To14 e3]
convertExpr0To14 (Resume e) =
  appsE [varE $ mkName "app14", appsE [conE $ mkName "Pure", varE $ mkName "resume"], convertExpr0To14 e]

newtype P14
  = P14 TH.Exp
  deriving (Show)

instance Ppr P14 where
  ppr (P14 e) = ppr e

testFile14 :: FilePath
testFile14 = "test-generated/Final/SmallToDeepTests14.hs"

testModule14 :: String
testModule14 = "Final.SmallToDeepTests14"

createTestString14 :: Int -> PG.Type -> Expr -> IO String
createTestString14 testIdx ty e =
  flip evalStateT (C14 [] [] testIdx 0) $ do
    e14 <- convertExpr0To14 e

    effs <- gets c14Effs
    decs <- gets c14Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "Result")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "convertResult14To0",
                appsE [varE $ mkName "eval14", return e14],
                createValueConversionFunction14 ty
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter14 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter14 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString14 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile14
    when fExists (removeFile testFile14)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile14
      ( "module "
          <> testModule14
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.SmallToDeep"
          <> "\n"
          <> "import Final.SmallToDeepTest (convertResult14To0, convertValue14To0Int, convertValue14To0List, convertValue14To0Pair, convertValue14To0Bool, convertValue14To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the evaler by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.SmallToDeep", "Final.SmallToDeepTest", testModule14]
  setImports ["Final.SmallToDeep", testModule14]

  -- Run the many tests in this test set by using many 'eval' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v0 = STD.normalise0 $ convertToExpr0 e
        v14 <- interpret ("p" <> show testIdx) (as :: STD.Result)
        return (liftBool (v0 == v14))
    )
    tes
    [1 ..]

testMany14 :: Int -> Property
testMany14 n = ioProperty $ do
  results <- runInterpreter tests
  case results of
    Left err -> return (property (exception (displayException err) (throw err)))
    Right props -> return $ conjoin $ concat props
  where
    (nBatches, leftover) = n `divMod` maxBatchSize
    batchSizes = replicate nBatches maxBatchSize <> [leftover | leftover > 0]
    tests =
      traverse
        ( \sz -> do
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndDeepExpr
            testBatchInterpreter14 tes
        )
        batchSizes
