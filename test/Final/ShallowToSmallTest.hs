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

module Final.ShallowToSmallTest where

import Control.Exception (displayException, throw)
import Control.Monad.State
import Final.ProgramGen as PG
import qualified Final.ShallowToSmall as STD
import Final.TestUtil
import Language.Haskell.Interpreter
import Language.Haskell.Interpreter.Extension
import Language.Haskell.TH as TH
import Test.QuickCheck.Property as QC (Result, exception, liftBool)
import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck hiding (elements)
import UnliftIO.Directory (createDirectoryIfMissing, doesFileExist, removeFile)

instance Eq STD.ValueOrOp6 where
  STD.NoOp6 v == STD.NoOp6 v' = v == v'
  _ == _ = False

-- Possible implementation for equality:
-- STD.Op6 op va x_op == STD.Op6 op' va' x_op' = op == op' && va == va' && x_op (Var "__special") == x_op' (Var "__special")

---------------------------------------------------------------
---- The list of tests to run
---------------------------------------------------------------
tests :: TestTree
tests =
  testGroup
    "Shallow to Small conversion"
    [ ignoreTest $
        testGroup
          "Program Generator"
          [ disableLongTests $
              testProperty
                "Program generation does not cause failure (big)"
                (programNeverErrorsProperty 20),
            testProperty
              "Program generation does not cause failure (small)"
              (programNeverErrorsProperty 12)
          ],
      testGroup
        "Generated"
        [ disableLongTests $
            testGroup
              "Equivalence of programs that need to be resynthesized"
              [ testProperty
                  "Equivalence of eval0 and interpret6_9"
                  (withMaxSuccess bigTestRepetitions $ testMany0 bigTestQuantity),
                testProperty
                  "Equivalence of eval1 and interpret6_9"
                  (withMaxSuccess bigTestRepetitions $ testMany1 bigTestQuantity),
                testProperty
                  "Equivalence of eval2 and interpret6_9"
                  (withMaxSuccess bigTestRepetitions $ testMany2 bigTestQuantity),
                testProperty
                  "Equivalence of eval3 and interpret6_9"
                  (withMaxSuccess bigTestRepetitions $ testMany3 bigTestQuantity),
                testProperty
                  "Equivalence of interpret4 and interpret6_9"
                  (withMaxSuccess bigTestRepetitions $ testMany4 bigTestQuantity)
              ],
          testProperty
            "Equivalence of interpret5 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id (convertVOP5ToVOP6 . STD.eval5 . convertToExpr5) (STD.normalise6_9 . convertToExpr6) arbitraryShallowExpr,
          testProperty
            "Equivalence of interpret6_1 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_1 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_2 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_2 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_3 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_3 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_4 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_4 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_5 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_5 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_6 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_6 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_7 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_7 STD.normalise6_9 expr6Gen,
          testProperty
            "Equivalence of interpret6_8 and interpret6_9"
            $ withMaxSuccess 10000
            $ programRunsTheSameProperty id STD.normalise6_8 STD.normalise6_9 expr6Gen
        ],
      testGroup
        "Manual"
        [ testCase "Normalise6_9 yields expected result" $
            void $
              traverse (\(e, v) -> STD.normalise6_9 e @?= STD.NoOp6 (convertToValue6 v)) ((\(TypeAndExpr _ e, v) -> (convertToExpr6 e, v)) <$> manualTestProgramsAndResults),
          disableLongTests $
            testGroup
              "Equivalence of programs that need to be resynthesized"
              [ testProperty
                  "Equivalence of normalise6_9 and run0"
                  ( ioProperty $ do
                      results <- runInterpreter (testBatchInterpreter0 manualTestPrograms)
                      case results of
                        Left err -> return (property (exception (displayException err) (throw err)))
                        Right v -> return (conjoin v)
                  ),
                testProperty
                  "Equivalence of normalise6_9 and run1"
                  ( ioProperty $ do
                      results <- runInterpreter (testBatchInterpreter1 manualTestPrograms)
                      case results of
                        Left err -> return (property (exception (displayException err) (throw err)))
                        Right v -> return (conjoin v)
                  ),
                testProperty
                  "Equivalence of normalise6_9 and run2"
                  ( ioProperty $ do
                      results <- runInterpreter (testBatchInterpreter2 manualTestPrograms)
                      case results of
                        Left err -> return (property (exception (displayException err) (throw err)))
                        Right v -> return (conjoin v)
                  ),
                testProperty
                  "Equivalence of normalise6_9 and run3"
                  ( ioProperty $ do
                      results <- runInterpreter (testBatchInterpreter3 manualTestPrograms)
                      case results of
                        Left err -> return (property (exception (displayException err) (throw err)))
                        Right v -> return (conjoin v)
                  ),
                testProperty
                  "Equivalence of normalise6_9 and run4"
                  ( ioProperty $ do
                      results <- runInterpreter (testBatchInterpreter4 manualTestPrograms)
                      case results of
                        Left err -> return (property (exception (displayException err) (throw err)))
                        Right v -> return (conjoin v)
                  )
              ],
          testCase "Equivalence of normalise6_9 and interpret5" $
            void $
              traverse (\e -> STD.normalise6_9 (convertToExpr6 e) @?= convertVOP5ToVOP6 (STD.eval5 (convertToExpr5 e))) (manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_1" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_1 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_2" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_2 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_3" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_3 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_4" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_4 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_5" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_5 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_6" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_6 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_7" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_7 e) (convertToExpr6 <$> manualTestProgramExprs),
          testCase "Equivalence of normalise6_9 and normalise6_8" $
            void $
              traverse (\e -> STD.normalise6_9 e @?= STD.normalise6_8 e) (convertToExpr6 <$> manualTestProgramExprs)
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
  withMaxSuccess 100000 $
    mapSize (const sz) $
      forAll expr6Gen $ \e -> case STD.normalise6_9 e of
        STD.NoOp6 _ -> True
        _ -> False

---------------------------------------------------------------
---- Manual testing programmes
---------------------------------------------------------------
manualTestProgramExprs :: [Expr]
manualTestProgramExprs = (\(TypeAndExpr _ e) -> e) <$> manualTestPrograms

manualTestPrograms :: [TypeAndExpr]
manualTestPrograms = fst <$> manualTestProgramsAndResults

-- data MTValue a where
--  MTUnitV :: MTValue ()
--
-- data MTHandler a w where
--  MTHandler ::
--    (forall x. eff x -> (x -> MTExpr (eff :++: r) a) -> (Suspended (MTExpr (eff :++: r) a) -> MTExpr r w) -> MTExpr r w) ->
--    (a -> MTExpr r w) ->
--    SHandler1 eff r a w
--
-- data MTExpr sig a where
--  MTLit :: MTValue a -> MTExprTree sig a
--  MTHandle :: MTHandler
--
-- mtToExpr :: MTExpr sig a -> Expr
-- mtToExpr e
--  where
--    toExpr :: Int -> MTExpr sig a -> Expr
--    toExpr nVars (MTLit v) =
--
--    toValue :: Int -> MTValue a -> Value
--    toValue nVars v = case v of
--      MTUnitV -> UnitV

manualTestProgramsAndResults :: [(TypeAndExpr, Value)]
manualTestProgramsAndResults =
  [ (TypeAndExpr UnitT (Lit UnitV), UnitV),
    ( TypeAndExpr
        IntT
        ( Handle
            ( Handler
                1
                [ OpI (OpType 1 0 UnitT IntT) (App Hdl (Lit (SuspendedV (Suspended (Resume (Lit (IntV 5)))))))
                ]
                (RetI (RetType 0 0 [] (PG.VarT 0) (EType [] (PG.VarT 0))) (Var 0))
            )
            (Lit (SuspendedV (Suspended (OpCall 1 1 (Lit UnitV)))))
        ),
      IntV 5
    )
  ]

---------------------------------------------------------------
---- Conversion from the generator expressions to STD.Expr6
---------------------------------------------------------------
convertToValue6 :: Value -> STD.Value6
convertToValue6 (LambdaV arg e) = STD.LambdaV6 (toVarName arg) (convertToExpr6 e)
convertToValue6 (IntV n) = STD.IntV6 n
convertToValue6 (BoolV n) = STD.BoolV6 n
convertToValue6 UnitV = STD.UnitV6
convertToValue6 (PairV v1 v2) = STD.PairV6 (convertToValue6 v1) (convertToValue6 v2)
convertToValue6 NilV = STD.NilV6
convertToValue6 (ConsV v1 v2) = STD.ConsV6 (convertToValue6 v1) (convertToValue6 v2)
convertToValue6 (SuspendedV (Suspended e)) = STD.suspend6 (convertToExpr6 e)

convertToHandler6 :: Handler -> STD.SHandler6
convertToHandler6 (Handler effIdx ops (RetI (RetType rArgIdx _ _ _ _) ret)) =
  STD.SHandler6
    (toEffName 6 effIdx)
    ((\(OpI (OpType opIdx argIdx _ _) e) -> STD.OpI6 (toOpName 6 effIdx opIdx) (toVarName argIdx) (convertToExpr6 e)) <$> ops)
    (STD.RetI6 (toVarName rArgIdx) (convertToExpr6 ret))

convertToUnOp6 :: UnOpOperator -> STD.UnOpOperator6
convertToUnOp6 Fst = STD.Fst6
convertToUnOp6 Snd = STD.Snd6

convertToBinOp6 :: BinOpOperator -> STD.BinOpOperator6
convertToBinOp6 Concat = STD.Concat6
convertToBinOp6 Add = STD.Add6
convertToBinOp6 Mul = STD.Mul6

convertToExpr6 :: Expr -> STD.Expr6
convertToExpr6 (Var idx) = STD.Var6 (toVarName idx)
convertToExpr6 (App e1 e2) = STD.App6 (convertToExpr6 e1) (convertToExpr6 e2)
convertToExpr6 (Let idx e1 e2) = STD.Let6 (toVarName idx) (convertToExpr6 e1) (convertToExpr6 e2)
convertToExpr6 (OpCall effIdx opIdx e) = STD.OpCall6 (toEffName 6 effIdx) (toOpName 6 effIdx opIdx) (convertToExpr6 e)
convertToExpr6 (Handle hlr e) = STD.SHandle6 (convertToHandler6 hlr) (convertToExpr6 e)
convertToExpr6 (Lit v) = STD.Lit6 (convertToValue6 v)
convertToExpr6 Hdl = STD.Var6 "hdl"
convertToExpr6 (If ec et ee) = STD.If6 (convertToExpr6 ec) (convertToExpr6 et) (convertToExpr6 ee)
convertToExpr6 (Pair e1 e2) = STD.Pair6 (convertToExpr6 e1) (convertToExpr6 e2)
convertToExpr6 (Cons e1 e2) = STD.Cons6 (convertToExpr6 e1) (convertToExpr6 e2)
convertToExpr6 (Resume e) = STD.App6 (STD.Var6 "resume") (convertToExpr6 e)
convertToExpr6 (UnOp unOp e) = STD.UnOp6 (convertToUnOp6 unOp) (convertToExpr6 e)
convertToExpr6 (BinOp e1 binOp e2) = STD.BinOp6 (convertToExpr6 e1) (convertToBinOp6 binOp) (convertToExpr6 e2)

expr6Gen :: Gen STD.Expr6
expr6Gen = convertToExpr6 <$> arbitraryShallowExpr

---------------------------------------------------------------
---- Conversion from the generator expressions to STD.Expr5
---------------------------------------------------------------
convertToValue5 :: Value -> STD.Value5
convertToValue5 (LambdaV arg e) = STD.LambdaV5 (toVarName arg) (convertToExpr5 e)
convertToValue5 (IntV n) = STD.IntV5 n
convertToValue5 (BoolV n) = STD.BoolV5 n
convertToValue5 UnitV = STD.UnitV5
convertToValue5 (PairV v1 v2) = STD.PairV5 (convertToValue5 v1) (convertToValue5 v2)
convertToValue5 NilV = STD.NilV5
convertToValue5 (ConsV v1 v2) = STD.ConsV5 (convertToValue5 v1) (convertToValue5 v2)
convertToValue5 (SuspendedV (Suspended e)) = STD.suspend5 (convertToExpr5 e)

convertToHandler5 :: Handler -> STD.SHandler5
convertToHandler5 (Handler effIdx ops (RetI (RetType rArgIdx _ _ _ _) ret)) =
  STD.SHandler5
    (toEffName 5 effIdx)
    ((\(OpI (OpType opIdx argIdx _ _) e) -> STD.OpI5 (toOpName 5 effIdx opIdx) (toVarName argIdx) (convertToExpr5 e)) <$> ops)
    (STD.RetI5 (toVarName rArgIdx) (convertToExpr5 ret))

convertToUnOp5 :: UnOpOperator -> STD.UnOpOperator5
convertToUnOp5 Fst = STD.Fst5
convertToUnOp5 Snd = STD.Snd5

convertToBinOp5 :: BinOpOperator -> STD.BinOpOperator5
convertToBinOp5 Concat = STD.Concat5
convertToBinOp5 Add = STD.Add5
convertToBinOp5 Mul = STD.Mul5

convertToExpr5 :: Expr -> STD.Expr5
convertToExpr5 (Var idx) = STD.Var5 (toVarName idx)
convertToExpr5 (App e1 e2) = STD.App5 (convertToExpr5 e1) (convertToExpr5 e2)
convertToExpr5 (Let idx e1 e2) = STD.Let5 (toVarName idx) (convertToExpr5 e1) (convertToExpr5 e2)
convertToExpr5 (OpCall effIdx opIdx e) = STD.OpCall5 (toEffName 5 effIdx) (toOpName 5 effIdx opIdx) (convertToExpr5 e)
convertToExpr5 (Handle hlr e) = STD.SHandle5 (convertToHandler5 hlr) (convertToExpr5 e)
convertToExpr5 (Lit v) = STD.Lit5 (convertToValue5 v)
convertToExpr5 Hdl = STD.Var5 "hdl"
convertToExpr5 (If ec et ee) = STD.If5 (convertToExpr5 ec) (convertToExpr5 et) (convertToExpr5 ee)
convertToExpr5 (Pair e1 e2) = STD.Pair5 (convertToExpr5 e1) (convertToExpr5 e2)
convertToExpr5 (Cons e1 e2) = STD.Cons5 (convertToExpr5 e1) (convertToExpr5 e2)
convertToExpr5 (Resume e) = STD.App5 (STD.Var5 "resume") (convertToExpr5 e)
convertToExpr5 (UnOp unOp e) = STD.UnOp5 (convertToUnOp5 unOp) (convertToExpr5 e)
convertToExpr5 (BinOp e1 binOp e2) = STD.BinOp5 (convertToExpr5 e1) (convertToBinOp5 binOp) (convertToExpr5 e2)

expr5Gen :: Gen STD.Expr5
expr5Gen = convertToExpr5 <$> arbitraryShallowExpr

convertValue5ToValue6 :: STD.Value5 -> STD.Value6
convertValue5ToValue6 (STD.IntV5 n) = STD.IntV6 n
convertValue5ToValue6 (STD.BoolV5 b) = STD.BoolV6 b
convertValue5ToValue6 (STD.PairV5 v1 v2) = STD.PairV6 (convertValue5ToValue6 v1) (convertValue5ToValue6 v2)
convertValue5ToValue6 STD.UnitV5 = STD.UnitV6
convertValue5ToValue6 STD.NilV5 = STD.NilV6
convertValue5ToValue6 (STD.ConsV5 v1 v2) = STD.ConsV6 (convertValue5ToValue6 v1) (convertValue5ToValue6 v2)

convertVOP5ToVOP6 :: STD.Result5 -> STD.ValueOrOp6
convertVOP5ToVOP6 (STD.NoOp5 v) = STD.NoOp6 (convertValue5ToValue6 v)

---------------------------------------------------------------
---- Conversion from the generator expressions to STD.Expr4
---------------------------------------------------------------
data C4 where
  C4 ::
    { c4Effs :: [TH.Dec],
      c4Where :: [TH.Dec],
      c4TIdx :: Int,
      c4RetIdx :: Int
    } ->
    C4

type R4 = StateT C4 IO

instance Quote R4 where
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

convertType0To4 :: (MonadState C4 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To4 _ = conT $ mkName "Value4"

convertEType0To4 :: (MonadState C4 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To4 (EType effs t) = conT $ mkName "Expr4"

convertEType0To4' :: (MonadState C4 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To4' (EType _ t) = conT $ mkName "Expr4"

convertSHandler0To4 :: (MonadState C4 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertSHandler0To4 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c4TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To4 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To4 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c4RetIdx)
  modify (\c4 -> c4 {c4RetIdx = c4RetIdx c4 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To4 argT, resT]) (appslT arrowT [convertType0To4 retArgType, convertEType0To4 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To4 eRet) []]

  modify (\c4 -> c4 {c4Effs = c4Effs c4 <> [], c4Where = c4Where c4 <> [retTD, retD]})

  appsE
    [ varE $ mkName "SHandler4",
      stringE $ toEffName tIdx effIdx,
      lamE [varP $ mkName "___op"] $
        caseE (varE $ mkName "___op") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match
                (litP $ stringL $ toOpName tIdx effIdx opIdx)
                ( normalB
                    $ lamE [varP $ mkName $ toVarName argIdx, varP $ mkName "resumeF", varP $ mkName "hdlF"]
                    $ letE
                      [ valD (varP $ mkName "resume") (normalB $ appsE [conE $ mkName "LambdaV4", varE $ mkName "resumeF"]) [],
                        valD (varP $ mkName "hdl") (normalB $ appsE [conE $ mkName "LambdaV4", varE $ mkName "hdlF"]) []
                      ]
                    $ convertExpr0To4 eOp
                )
                []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To4 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To4 Fst = varE $ mkName "Fst4"
convertUnOp0To4 Snd = varE $ mkName "Snd4"

convertBinOp0To4 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To4 Concat = varE $ mkName "Concat4"
convertBinOp0To4 Add = varE $ mkName "Add4"
convertBinOp0To4 Mul = varE $ mkName "Mul4"

convertValue0To4 :: (MonadState C4 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To4 (LambdaV nm e) =
  appsE [varE $ mkName "LambdaV4", lamE [varP $ mkName $ toVarName nm] $ convertExpr0To4 e]
convertValue0To4 (IntV i) =
  appsE [varE $ mkName "IntV4", litE $ integerL $ toInteger i]
convertValue0To4 UnitV = varE $ mkName "UnitV4"
convertValue0To4 (BoolV b) =
  appsE [varE $ mkName "BoolV4", varE $ mkName $ show b]
convertValue0To4 (PairV v1 v2) =
  appsE [varE $ mkName "PairV4", convertValue0To4 v1, convertValue0To4 v2]
convertValue0To4 NilV =
  varE $ mkName "NilV4"
convertValue0To4 (ConsV v1 v2) =
  appsE [varE $ mkName "ConsV4", convertValue0To4 v1, convertValue0To4 v2]
convertValue0To4 (SuspendedV (Suspended e)) =
  appsE [varE $ mkName "suspend4", convertExpr0To4 e]

convertExpr0To4 :: (MonadState C4 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To4 (Var varIdx) =
  appsE [conE $ mkName "Lit4", varE $ mkName $ toVarName varIdx]
convertExpr0To4 (App e1 e2) =
  appsE [varE $ mkName "App4", convertExpr0To4 e1, convertExpr0To4 e2]
convertExpr0To4 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let4", convertExpr0To4 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To4 e2]
convertExpr0To4 (OpCall effIdx opIdx e) = do
  tIdx <- gets c4TIdx
  appsE [varE $ mkName "OpCall4", stringE $ toEffName tIdx effIdx, stringE $ toOpName tIdx effIdx opIdx, convertExpr0To4 e]
convertExpr0To4 (Handle h e) =
  appsE [conE $ mkName "SHandle4", convertSHandler0To4 h, convertExpr0To4 e]
convertExpr0To4 (Lit v) =
  appsE [conE $ mkName "Lit4", convertValue0To4 v]
convertExpr0To4 Hdl =
  appsE [conE $ mkName "Lit4", varE $ mkName "hdl"]
convertExpr0To4 (Pair e1 e2) =
  appsE [varE $ mkName "Pair4", convertExpr0To4 e1, convertExpr0To4 e2]
convertExpr0To4 (Cons e1 e2) =
  appsE [varE $ mkName "Cons4", convertExpr0To4 e1, convertExpr0To4 e2]
convertExpr0To4 (UnOp uop e) =
  appsE [varE $ mkName "UnOp4", convertUnOp0To4 uop, convertExpr0To4 e]
convertExpr0To4 (BinOp e1 bop e2) =
  appsE [varE $ mkName "BinOp4", convertExpr0To4 e1, convertBinOp0To4 bop, convertExpr0To4 e2]
convertExpr0To4 (If e1 e2 e3) =
  appsE [varE $ mkName "If4", convertExpr0To4 e1, convertExpr0To4 e2, convertExpr0To4 e3]
convertExpr0To4 (Resume e) =
  appsE [varE $ mkName "App4", appsE [conE $ mkName "Lit4", varE $ mkName "resume"], convertExpr0To4 e]

newtype P4
  = P4 TH.Exp
  deriving (Show)

instance Ppr P4 where
  ppr (P4 e) = ppr e

testFile4 :: FilePath
testFile4 = "test-generated/Final/ShallowToSmallTests4.hs"

testModule4 :: String
testModule4 = "Final.ShallowToSmallTests4"

createTestString4 :: Int -> PG.Type -> Expr -> IO String
createTestString4 testIdx ty e =
  flip evalStateT (C4 [] [] testIdx 0) $ do
    e4 <- convertExpr0To4 e

    effs <- gets c4Effs
    decs <- gets c4Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "ValueOrOp6")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE [varE $ mkName "convertVOP4ToVOP6", appsE [varE $ mkName "eval4", return e4]]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter4 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter4 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString4 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile4
    when fExists (removeFile testFile4)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile4
      ( "module "
          <> testModule4
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.ShallowToSmall"
          <> "\n"
          <> "import Final.ShallowToSmallTest (convertVOP4ToVOP6)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the interpreter by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.ShallowToSmall", "Final.ShallowToSmallTest", testModule4]
  setImports ["Final.ShallowToSmall", testModule4]

  -- Run the many tests in this test set by using many 'interpret' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v6 = STD.normalise6_9 $ convertToExpr6 e
        v4 <- interpret ("p" <> show testIdx) (as :: STD.ValueOrOp6)
        return (liftBool (v6 == v4))
    )
    tes
    [1 ..]

testMany4 :: Int -> Property
testMany4 n = ioProperty $ do
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
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndShallowExpr
            testBatchInterpreter4 tes
        )
        batchSizes

convertValue4ToValue6 :: STD.Value4 -> STD.Value6
convertValue4ToValue6 (STD.IntV4 n) = STD.IntV6 n
convertValue4ToValue6 (STD.BoolV4 b) = STD.BoolV6 b
convertValue4ToValue6 (STD.PairV4 v1 v2) = STD.PairV6 (convertValue4ToValue6 v1) (convertValue4ToValue6 v2)
convertValue4ToValue6 STD.UnitV4 = STD.UnitV6
convertValue4ToValue6 STD.NilV4 = STD.NilV6
convertValue4ToValue6 (STD.ConsV4 v1 v2) = STD.ConsV6 (convertValue4ToValue6 v1) (convertValue4ToValue6 v2)

convertVOP4ToVOP6 :: STD.Result4 -> STD.ValueOrOp6
convertVOP4ToVOP6 (STD.NoOp4 v) = STD.NoOp6 (convertValue4ToValue6 v)

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr3
---------------------------------------------------------------
data C3 where
  C3 ::
    { c3Effs :: [TH.Dec],
      c3Where :: [TH.Dec],
      c3TIdx :: Int,
      c3RetIdx :: Int
    } ->
    C3

type R3 = StateT C3 IO

instance Quote R3 where
  newName = lift . newName

convertType0To3 :: (MonadState C3 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To3 t = appslT (conT $ mkName "Value3") [convertType0To3' t]

convertType0To3' :: (MonadState C3 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To3' (FunT argT retT) = appslT arrowT [convertType0To3' argT, convertEType0To3 retT]
convertType0To3' IntT = varT $ mkName "Int"
convertType0To3' BoolT = varT $ mkName "Bool"
convertType0To3' UnitT = varT $ mkName "()"
convertType0To3' (PairT t1 t2) = appslT (tupleT 2) [convertType0To3' t1, convertType0To3' t2]
convertType0To3' (PG.ListT t) = appslT listT [convertType0To3' t]
convertType0To3' (PG.VarT n) = varT $ mkName $ toTyVarName n
convertType0To3' (SuspendedT effs t) = appT (conT $ mkName "Suspended") (convertEType0To3 (EType effs t))

convertEType0To3 :: (MonadState C3 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To3 (EType effs t) = do
  tIdx <- gets c3TIdx
  appslT
    (conT (mkName "Expr3"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To3' t
    ]

convertEType0To3' :: (MonadState C3 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To3' (EType _ t) = do
  appslT
    (conT (mkName "Expr3"))
    [ varT $ mkName "sig",
      convertType0To3' t
    ]

convertHandler0To3 :: (MonadState C3 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To3 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c3TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To3 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To3' opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c3RetIdx)
  modify (\c3 -> c3 {c3RetIdx = c3RetIdx c3 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To3 argT, resT]) (appslT arrowT [convertType0To3 retArgType, convertEType0To3 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To3 eRet) []]

  modify (\c3 -> c3 {c3Effs = c3Effs c3 <> [dd], c3Where = c3Where c3 <> [retTD, retD]})

  appsE
    [ varE $ mkName "SHandler3",
      lamE [varP $ mkName "opArg", varP $ mkName "resumeF", varP $ mkName "hdlF"]
        $ letE
          [ valD (varP $ mkName "resume") (normalB $ appsE [conE $ mkName "LambdaV3", varE $ mkName "resumeF"]) [],
            valD (varP $ mkName "hdl") (normalB $ appsE [conE $ mkName "LambdaV3", varE $ mkName "hdlF"]) []
          ]
        $ caseE (varE $ mkName "opArg")
        $ ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To3 eOp) []
          )
          <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To3 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To3 Fst = varE $ mkName "Fst3"
convertUnOp0To3 Snd = varE $ mkName "Snd3"

convertBinOp0To3 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To3 Concat = varE $ mkName "Concat3"
convertBinOp0To3 Add = varE $ mkName "Add3"
convertBinOp0To3 Mul = varE $ mkName "Mul3"

convertResult3To6 :: STD.Result3 sig a -> STD.ValueOrOp6
convertResult3To6 (STD.NoOp3 v) = STD.NoOp6 $ convertValue3To6 v
convertResult3To6 (STD.Op3 _ _) = error "Invalid [3], an operation was left unhandled"

convertValue3To6 :: STD.Value3 a -> STD.Value6
convertValue3To6 (STD.IntV3 v) = STD.IntV6 v
convertValue3To6 (STD.BoolV3 v) = STD.BoolV6 v
convertValue3To6 STD.NilV3 = STD.NilV6
convertValue3To6 STD.UnitV3 = STD.UnitV6
convertValue3To6 (STD.PairV3 v1 v2) = STD.PairV6 (convertValue3To6 v1) (convertValue3To6 v2)
convertValue3To6 (STD.ConsV3 v1 v2) = STD.ConsV6 (convertValue3To6 v1) (convertValue3To6 v2)

convertValue0To3 :: (MonadState C3 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To3 (LambdaV nm e) =
  appsE [varE $ mkName "LambdaV3", lamE [varP $ mkName $ toVarName nm] $ convertExpr0To3 e]
convertValue0To3 (IntV i) =
  appsE [varE $ mkName "IntV3", litE $ integerL $ toInteger i]
convertValue0To3 UnitV = varE $ mkName "UnitV3"
convertValue0To3 (BoolV b) =
  appsE [varE $ mkName "BoolV3", varE $ mkName $ show b]
convertValue0To3 (PairV v1 v2) =
  appsE [varE $ mkName "PairV3", convertValue0To3 v1, convertValue0To3 v2]
convertValue0To3 NilV =
  varE $ mkName "NilV3"
convertValue0To3 (ConsV v1 v2) =
  appsE [varE $ mkName "ConsV3", convertValue0To3 v1, convertValue0To3 v2]
convertValue0To3 (SuspendedV (Suspended e)) =
  appsE [varE $ mkName "suspend3", convertExpr0To3 e]

convertExpr0To3 :: (MonadState C3 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To3 (Var varIdx) =
  appsE [conE $ mkName "Lit3", varE $ mkName $ toVarName varIdx]
convertExpr0To3 (App e1 e2) =
  appsE [varE $ mkName "App3", convertExpr0To3 e1, convertExpr0To3 e2]
convertExpr0To3 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let3", convertExpr0To3 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To3 e2]
convertExpr0To3 (OpCall effIdx opIdx e) = do
  tIdx <- gets c3TIdx
  appsE [varE $ mkName "opCall3", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To3 e]
convertExpr0To3 (Handle h e) =
  appsE [conE $ mkName "SHandle3", convertHandler0To3 h, convertExpr0To3 e]
convertExpr0To3 (Lit v) =
  appsE [conE $ mkName "Lit3", convertValue0To3 v]
convertExpr0To3 Hdl =
  appsE [conE $ mkName "Lit3", varE $ mkName "hdl"]
convertExpr0To3 (Pair e1 e2) =
  appsE [varE $ mkName "Pair3", convertExpr0To3 e1, convertExpr0To3 e2]
convertExpr0To3 (Cons e1 e2) =
  appsE [varE $ mkName "Cons3", convertExpr0To3 e1, convertExpr0To3 e2]
convertExpr0To3 (UnOp uop e) =
  appsE [varE $ mkName "UnOp3", convertUnOp0To3 uop, convertExpr0To3 e]
convertExpr0To3 (BinOp e1 bop e2) =
  appsE [varE $ mkName "BinOp3", convertExpr0To3 e1, convertBinOp0To3 bop, convertExpr0To3 e2]
convertExpr0To3 (If e1 e2 e3) =
  appsE [varE $ mkName "If3", convertExpr0To3 e1, convertExpr0To3 e2, convertExpr0To3 e3]
convertExpr0To3 (Resume e) =
  appsE [varE $ mkName "App3", appsE [conE $ mkName "Lit3", varE $ mkName "resume"], convertExpr0To3 e]

newtype P3
  = P3 TH.Exp
  deriving (Show)

instance Ppr P3 where
  ppr (P3 e) = ppr e

testFile3 :: FilePath
testFile3 = "test-generated/Final/ShallowToSmallTests3.hs"

testModule3 :: String
testModule3 = "Final.ShallowToSmallTests3"

createTestString3 :: Int -> PG.Type -> Expr -> IO String
createTestString3 testIdx ty e =
  flip evalStateT (C3 [] [] testIdx 0) $ do
    e3 <- convertExpr0To3 e

    effs <- gets c3Effs
    decs <- gets c3Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "ValueOrOp6")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE [varE $ mkName "convertResult3To6", appsE [varE $ mkName "eval3", return e3]]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter3 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter3 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString3 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile3
    when fExists (removeFile testFile3)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile3
      ( "module "
          <> testModule3
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.ShallowToSmall"
          <> "\n"
          <> "import Final.ShallowToSmallTest (convertResult3To6)"
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
  loadModules ["Final.ShallowToSmall", "Final.ShallowToSmallTest", testModule3]
  setImports ["Final.ShallowToSmall", testModule3]

  -- Run the many tests in this test set by using many 'interpret' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v6 = STD.normalise6_9 $ convertToExpr6 e
        v3 <- interpret ("p" <> show testIdx) (as :: STD.ValueOrOp6)
        return (liftBool (v6 == v3))
    )
    tes
    [1 ..]

testMany3 :: Int -> Property
testMany3 n = ioProperty $ do
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
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndShallowExpr
            testBatchInterpreter3 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr2
---------------------------------------------------------------
data C2 where
  C2 ::
    { c2Effs :: [TH.Dec],
      c2Where :: [TH.Dec],
      c2TIdx :: Int,
      c2RetIdx :: Int
    } ->
    C2

type R2 = StateT C2 IO

instance Quote R2 where
  newName = lift . newName

convertType0To2 :: (MonadState C2 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To2 (FunT argT retT) = appslT arrowT [convertType0To2 argT, convertEType0To2 retT]
convertType0To2 IntT = varT $ mkName "Int"
convertType0To2 BoolT = varT $ mkName "Bool"
convertType0To2 UnitT = varT $ mkName "()"
convertType0To2 (PairT t1 t2) = appslT (tupleT 2) [convertType0To2 t1, convertType0To2 t2]
convertType0To2 (PG.ListT t) = appslT listT [convertType0To2 t]
convertType0To2 (PG.VarT n) = varT $ mkName $ toTyVarName n
convertType0To2 (SuspendedT effs t) = appT (conT $ mkName "Suspended") (convertEType0To2 (EType effs t))

convertEType0To2 :: (MonadState C2 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To2 (EType effs t) = do
  tIdx <- gets c2TIdx
  appslT
    (conT (mkName "Expr2"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To2 t
    ]

convertHandler0To2 :: (MonadState C2 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To2 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c2TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To2 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To2 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c2RetIdx)
  modify (\c2 -> c2 {c2RetIdx = c2RetIdx c2 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To2 argT, resT]) (appslT arrowT [convertType0To2 retArgType, convertEType0To2 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To2 eRet) []]

  modify (\c2 -> c2 {c2Effs = c2Effs c2 <> [dd], c2Where = c2Where c2 <> [retTD, retD]})

  appsE
    [ varE $ mkName "SHandler2",
      lamE [varP $ mkName "opArg", varP $ mkName "resume", varP $ mkName "hdl"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To2 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To2 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To2 Fst = varE $ mkName "Fst2"
convertUnOp0To2 Snd = varE $ mkName "Snd2"

convertBinOp0To2 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To2 Concat = varE $ mkName "Concat2"
convertBinOp0To2 Add = varE $ mkName "Add2"
convertBinOp0To2 Mul = varE $ mkName "Mul2"

convertResult2To0 :: STD.Result2 sig a -> (a -> STD.Value6) -> STD.ValueOrOp6
convertResult2To0 (STD.NoOp2 v) convert = STD.NoOp6 $ convert v
convertResult2To0 (STD.Op2 _ _) _ = error "Invalid [2], an operation was left unhandled"

convertValue2To0Int :: Int -> STD.Value6
convertValue2To0Int = STD.IntV6

convertValue2To0Bool :: Bool -> STD.Value6
convertValue2To0Bool = STD.BoolV6

convertValue2To0Unit :: () -> STD.Value6
convertValue2To0Unit _ = STD.UnitV6

convertValue2To0List :: (a -> STD.Value6) -> [a] -> STD.Value6
convertValue2To0List _ [] = STD.NilV6
convertValue2To0List fa (a : as) = STD.ConsV6 (fa a) (convertValue2To0List fa as)

convertValue2To0Pair :: (a -> STD.Value6) -> (b -> STD.Value6) -> (a, b) -> STD.Value6
convertValue2To0Pair fa fb (a, b) = STD.PairV6 (fa a) (fb b)

createValueConversionFunction2 :: (MonadState C2 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction2 IntT = varE $ mkName "convertValue2To0Int"
createValueConversionFunction2 BoolT = varE $ mkName "convertValue2To0Bool"
createValueConversionFunction2 UnitT = varE $ mkName "convertValue2To0Unit"
createValueConversionFunction2 (PairT t1 t2) = appsE [varE $ mkName "convertValue2To0Pair", createValueConversionFunction2 t1, createValueConversionFunction2 t2]
createValueConversionFunction2 (PG.ListT t) = appsE [varE $ mkName "convertValue2To0List", createValueConversionFunction2 t]

convertValue0To2 :: (MonadState C2 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To2 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To2 e
convertValue0To2 (IntV i) = litE $ integerL $ toInteger i
convertValue0To2 UnitV = conE $ mkName "()"
convertValue0To2 (BoolV b) = varE $ mkName $ show b
convertValue0To2 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To2 v1, convertValue0To2 v2]
convertValue0To2 NilV = conE $ mkName "[]"
convertValue0To2 (ConsV v1 v2) = infixE (Just $ convertValue0To2 v1) (varE $ mkName ":") (Just $ convertValue0To2 v2)
convertValue0To2 (SuspendedV (Suspended e)) = appsE [varE $ mkName "suspend", convertExpr0To2 e]

convertExpr0To2 :: (MonadState C2 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To2 (Var varIdx) =
  appsE [conE $ mkName "Lit2", varE $ mkName $ toVarName varIdx]
convertExpr0To2 (App e1 e2) =
  appsE [varE $ mkName "app2", convertExpr0To2 e1, convertExpr0To2 e2]
convertExpr0To2 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let2", convertExpr0To2 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To2 e2]
convertExpr0To2 (OpCall effIdx opIdx e) = do
  tIdx <- gets c2TIdx
  appsE [varE $ mkName "opCall2", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To2 e]
convertExpr0To2 (Handle h e) =
  appsE [conE $ mkName "SHandle2", convertHandler0To2 h, convertExpr0To2 e]
convertExpr0To2 (Lit v) =
  appsE [conE $ mkName "Lit2", convertValue0To2 v]
convertExpr0To2 Hdl =
  appsE [conE $ mkName "Lit2", varE $ mkName "hdl"]
convertExpr0To2 (Pair e1 e2) =
  appsE [varE $ mkName "pair2", convertExpr0To2 e1, convertExpr0To2 e2]
convertExpr0To2 (Cons e1 e2) =
  appsE [varE $ mkName "cons2", convertExpr0To2 e1, convertExpr0To2 e2]
convertExpr0To2 (UnOp uop e) =
  appsE [varE $ mkName "unOp2", convertUnOp0To2 uop, convertExpr0To2 e]
convertExpr0To2 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp2", convertExpr0To2 e1, convertBinOp0To2 bop, convertExpr0To2 e2]
convertExpr0To2 (If e1 e2 e3) =
  appsE [varE $ mkName "if2", convertExpr0To2 e1, convertExpr0To2 e2, convertExpr0To2 e3]
convertExpr0To2 (Resume e) =
  appsE [varE $ mkName "app2", appsE [conE $ mkName "Lit2", varE $ mkName "resume"], convertExpr0To2 e]

newtype P2
  = P2 TH.Exp
  deriving (Show)

instance Ppr P2 where
  ppr (P2 e) = ppr e

testFile2 :: FilePath
testFile2 = "test-generated/Final/ShallowToSmallTests2.hs"

testModule2 :: String
testModule2 = "Final.ShallowToSmallTests2"

createTestString2 :: Int -> PG.Type -> Expr -> IO String
createTestString2 testIdx ty e =
  flip evalStateT (C2 [] [] testIdx 0) $ do
    e2 <- convertExpr0To2 e

    effs <- gets c2Effs
    decs <- gets c2Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "ValueOrOp6")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "NoOp6",
                appsE
                  [ createValueConversionFunction2 ty,
                    appsE [varE $ mkName "run2", return e2]
                  ]
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter2 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter2 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString2 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile2
    when fExists (removeFile testFile2)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile2
      ( "module "
          <> testModule2
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.ShallowToSmall"
          <> "\n"
          <> "import Final.ShallowToSmallTest (convertValue2To0Int, convertValue2To0Bool, convertValue2To0Pair, convertValue2To0List, convertValue2To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the interpreter by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.ShallowToSmall", "Final.ShallowToSmallTest", testModule2]
  setImports ["Final.ShallowToSmall", testModule2]

  -- Run the many tests in this test set by using many 'interpret' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v6 = STD.normalise6_9 $ convertToExpr6 e
        v2 <- interpret ("p" <> show testIdx) (as :: STD.ValueOrOp6)
        return (liftBool (v6 == v2))
    )
    tes
    [1 ..]

testMany2 :: Int -> Property
testMany2 n = ioProperty $ do
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
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndShallowExpr
            testBatchInterpreter2 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr1
---------------------------------------------------------------
data C1 where
  C1 ::
    { c1Effs :: [TH.Dec],
      c1Where :: [TH.Dec],
      c1TIdx :: Int,
      c1RetIdx :: Int
    } ->
    C1

type R1 = StateT C1 IO

instance Quote R1 where
  newName = lift . newName

convertType0To1 :: (MonadState C1 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To1 (FunT argT retT) = appslT arrowT [convertType0To1 argT, convertEType0To1 retT]
convertType0To1 IntT = varT $ mkName "Int"
convertType0To1 BoolT = varT $ mkName "Bool"
convertType0To1 UnitT = varT $ mkName "()"
convertType0To1 (PairT t1 t2) = appslT (tupleT 2) [convertType0To1 t1, convertType0To1 t2]
convertType0To1 (PG.ListT t) = appslT listT [convertType0To1 t]
convertType0To1 (PG.VarT n) = varT $ mkName $ toTyVarName n
convertType0To1 (SuspendedT effs t) = appT (conT $ mkName "Suspended") (convertEType0To1 (EType effs t))

convertEType0To1 :: (MonadState C1 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To1 (EType effs t) = do
  tIdx <- gets c1TIdx
  appslT
    (conT (mkName "Expr1"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To1 t
    ]

convertHandler0To1 :: (MonadState C1 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To1 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c1TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To1 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To1 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c1RetIdx)
  modify (\c1 -> c1 {c1RetIdx = c1RetIdx c1 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To1 argT, resT]) (appslT arrowT [convertType0To1 retArgType, convertEType0To1 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To1 eRet) []]

  modify (\c1 -> c1 {c1Effs = c1Effs c1 <> [dd], c1Where = c1Where c1 <> [retTD, retD]})

  appsE
    [ varE $ mkName "SHandler1",
      lamE [varP $ mkName "opArg", varP $ mkName "resume", varP $ mkName "hdl"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To1 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To1 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To1 Fst = varE $ mkName "fst"
convertUnOp0To1 Snd = varE $ mkName "snd"

convertBinOp0To1 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To1 Concat = varE $ mkName "++"
convertBinOp0To1 Add = varE $ mkName "+"
convertBinOp0To1 Mul = varE $ mkName "*"

convertValue1To0Int :: Int -> STD.Value6
convertValue1To0Int = STD.IntV6

convertValue1To0Bool :: Bool -> STD.Value6
convertValue1To0Bool = STD.BoolV6

convertValue1To0Unit :: () -> STD.Value6
convertValue1To0Unit _ = STD.UnitV6

convertValue1To0List :: (a -> STD.Value6) -> [a] -> STD.Value6
convertValue1To0List _ [] = STD.NilV6
convertValue1To0List fa (a : as) = STD.ConsV6 (fa a) (convertValue1To0List fa as)

convertValue1To0Pair :: (a -> STD.Value6) -> (b -> STD.Value6) -> (a, b) -> STD.Value6
convertValue1To0Pair fa fb (a, b) = STD.PairV6 (fa a) (fb b)

createValueConversionFunction1 :: (MonadState C1 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction1 IntT = varE $ mkName "convertValue1To0Int"
createValueConversionFunction1 BoolT = varE $ mkName "convertValue1To0Bool"
createValueConversionFunction1 UnitT = varE $ mkName "convertValue1To0Unit"
createValueConversionFunction1 (PairT t1 t2) = appsE [varE $ mkName "convertValue1To0Pair", createValueConversionFunction1 t1, createValueConversionFunction1 t2]
createValueConversionFunction1 (PG.ListT t) = appsE [varE $ mkName "convertValue1To0List", createValueConversionFunction1 t]

convertValue0To1 :: (MonadState C1 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To1 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To1 e
convertValue0To1 (IntV i) = litE $ integerL $ toInteger i
convertValue0To1 UnitV = conE $ mkName "()"
convertValue0To1 (BoolV b) = varE $ mkName $ show b
convertValue0To1 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To1 v1, convertValue0To1 v2]
convertValue0To1 NilV = conE $ mkName "[]"
convertValue0To1 (ConsV v1 v2) = infixE (Just $ convertValue0To1 v1) (varE $ mkName ":") (Just $ convertValue0To1 v2)
convertValue0To1 (SuspendedV (Suspended e)) = appsE [varE $ mkName "suspend", convertExpr0To1 e]

convertExpr0To1 :: (MonadState C1 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To1 (Var varIdx) =
  appsE [conE $ mkName "Lit1", varE $ mkName $ toVarName varIdx]
convertExpr0To1 (App e1 e2) =
  appsE [varE $ mkName "app1", convertExpr0To1 e1, convertExpr0To1 e2]
convertExpr0To1 (Let argIdx e1 e2) =
  appsE [conE $ mkName "Let1", convertExpr0To1 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To1 e2]
convertExpr0To1 (OpCall effIdx opIdx e) = do
  tIdx <- gets c1TIdx
  appsE [varE $ mkName "opCall1", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To1 e]
convertExpr0To1 (Handle h e) =
  appsE [varE $ mkName "sHandle1", convertHandler0To1 h, convertExpr0To1 e]
convertExpr0To1 (Lit v) =
  appsE [conE $ mkName "Lit1", convertValue0To1 v]
convertExpr0To1 Hdl =
  appsE [conE $ mkName "Lit1", varE $ mkName "hdl"]
convertExpr0To1 (Pair e1 e2) =
  appsE [varE $ mkName "pair1", convertExpr0To1 e1, convertExpr0To1 e2]
convertExpr0To1 (Cons e1 e2) =
  appsE [varE $ mkName "cons1", convertExpr0To1 e1, convertExpr0To1 e2]
convertExpr0To1 (UnOp uop e) =
  appsE [varE $ mkName "unOp1", convertUnOp0To1 uop, convertExpr0To1 e]
convertExpr0To1 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp1", convertExpr0To1 e1, convertBinOp0To1 bop, convertExpr0To1 e2]
convertExpr0To1 (If e1 e2 e3) =
  appsE [varE $ mkName "if1", convertExpr0To1 e1, convertExpr0To1 e2, convertExpr0To1 e3]
convertExpr0To1 (Resume e) =
  appsE [varE $ mkName "app1", appsE [conE $ mkName "Lit1", varE $ mkName "resume"], convertExpr0To1 e]

newtype P1
  = P1 TH.Exp
  deriving (Show)

instance Ppr P1 where
  ppr (P1 e) = ppr e

testFile1 :: FilePath
testFile1 = "test-generated/Final/ShallowToSmallTests1.hs"

testModule1 :: String
testModule1 = "Final.ShallowToSmallTests1"

createTestString1 :: Int -> PG.Type -> Expr -> IO String
createTestString1 testIdx ty e =
  flip evalStateT (C1 [] [] testIdx 0) $ do
    e1 <- convertExpr0To1 e

    effs <- gets c1Effs
    decs <- gets c1Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "ValueOrOp6")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "NoOp6",
                appsE
                  [ createValueConversionFunction1 ty,
                    appsE [varE $ mkName "run1", return e1]
                  ]
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter1 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter1 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString1 testIdx ty e) tes [1 ..]
  liftIO $ do
    fExists <- doesFileExist testFile1
    when fExists (removeFile testFile1)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile1
      ( "module "
          <> testModule1
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.ShallowToSmall"
          <> "\n"
          <> "import Final.ShallowToSmallTest (convertValue1To0Int, convertValue1To0Bool, convertValue1To0Pair, convertValue1To0List, convertValue1To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the interpreter by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.ShallowToSmall", "Final.ShallowToSmallTest", testModule1]
  setImports ["Final.ShallowToSmall", testModule1]

  -- Run the many tests in this test set by using many 'interpret' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v6 = STD.normalise6_9 $ convertToExpr6 e
        v1 <- interpret ("p" <> show testIdx) (as :: STD.ValueOrOp6)
        return (liftBool (v6 == v1))
    )
    tes
    [1 ..]

testMany1 :: Int -> Property
testMany1 n = ioProperty $ do
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
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndShallowExpr
            testBatchInterpreter1 tes
        )
        batchSizes

---------------------------------------------------------------
---- Conversion from the Expr to STD.Expr0
---------------------------------------------------------------
data C0 where
  C0 ::
    { c0Effs :: [TH.Dec],
      c0Where :: [TH.Dec],
      c0TIdx :: Int,
      c0RetIdx :: Int
    } ->
    C0

type R0 = StateT C0 IO

instance Quote R0 where
  newName = lift . newName

convertType0To0 :: (MonadState C0 m, MonadIO m, Quote m) => PG.Type -> m TH.Type
convertType0To0 (FunT argT retT) = appslT arrowT [convertType0To0 argT, convertEType0To0 retT]
convertType0To0 IntT = varT $ mkName "Int"
convertType0To0 BoolT = varT $ mkName "Bool"
convertType0To0 UnitT = varT $ mkName "()"
convertType0To0 (PairT t1 t2) = appslT (tupleT 2) [convertType0To0 t1, convertType0To0 t2]
convertType0To0 (PG.ListT t) = appslT listT [convertType0To0 t]
convertType0To0 (PG.VarT n) = varT $ mkName $ toTyVarName n
convertType0To0 (SuspendedT effs t) = convertEType0To0 (EType effs t)

convertEType0To0 :: (MonadState C0 m, MonadIO m, Quote m) => PG.EType -> m TH.Type
convertEType0To0 (EType effs t) = do
  tIdx <- gets c0TIdx
  appslT
    (conT (mkName "Freer"))
    [ foldr
        ( \(EffType effIdx _ _ _) r ->
            infixT (conT $ mkName $ toEffName tIdx effIdx) (mkName ":++:") r
        )
        (conT $ mkName "EPure")
        (reverse effs),
      convertType0To0 t
    ]

convertHandler0To0 :: (MonadState C0 m, MonadIO m, Quote m) => Handler -> m TH.Exp
convertHandler0To0 (Handler effIdx ops (RetI (RetType retArgIdx _ retNv retArgType retType) eRet)) = do
  tIdx <- gets c0TIdx

  dd <-
    dataD
      (return [])
      (mkName $ toEffName tIdx effIdx)
      [plainTV $ mkName "a"]
      Nothing
      ( ( \(OpI (OpType opIdx _ opArgT opResT) _) ->
            gadtC
              [mkName $ toOpName tIdx effIdx opIdx]
              [simpleBT $ convertType0To0 opArgT]
              (appslT (varT $ mkName $ toEffName tIdx effIdx) [convertType0To0 opResT])
        )
          <$> ops
      )
      []

  retNm <- gets (("ret" <>) . show . c0RetIdx)
  modify (\c0 -> c0 {c0RetIdx = c0RetIdx c0 + 1})
  retTD <- sigD (mkName retNm) (foldr (\argT resT -> appslT arrowT [convertType0To0 argT, resT]) (appslT arrowT [convertType0To0 retArgType, convertEType0To0 retType]) retNv)
  retD <- funD (mkName retNm) [clause [varP $ mkName $ toVarName idx | idx <- [0 .. retArgIdx]] (normalB $ convertExpr0To0 eRet) []]

  modify (\c0 -> c0 {c0Effs = c0Effs c0 <> [dd], c0Where = c0Where c0 <> [retTD, retD]})

  appsE
    [ varE $ mkName "SHandler0",
      lamE [varP $ mkName "opArg", varP $ mkName "resume", varP $ mkName "hdl"] $
        caseE (varE $ mkName "opArg") $
          ( \(OpI (OpType opIdx argIdx _ _) eOp) ->
              match (conP (mkName $ toOpName tIdx effIdx opIdx) [varP $ mkName $ toVarName argIdx]) (normalB $ convertExpr0To0 eOp) []
          )
            <$> ops,
      appsE $ varE (mkName retNm) : [varE $ mkName $ toVarName idx | idx <- [0 .. retArgIdx - 1]]
    ]

convertUnOp0To0 :: (Quote m) => UnOpOperator -> m TH.Exp
convertUnOp0To0 Fst = varE $ mkName "fst"
convertUnOp0To0 Snd = varE $ mkName "snd"

convertBinOp0To0 :: (Quote m) => BinOpOperator -> m TH.Exp
convertBinOp0To0 Concat = varE $ mkName "++"
convertBinOp0To0 Add = varE $ mkName "+"
convertBinOp0To0 Mul = varE $ mkName "*"

convertValue0To0Int :: Int -> STD.Value6
convertValue0To0Int = STD.IntV6

convertValue0To0Bool :: Bool -> STD.Value6
convertValue0To0Bool = STD.BoolV6

convertValue0To0Unit :: () -> STD.Value6
convertValue0To0Unit _ = STD.UnitV6

convertValue0To0List :: (a -> STD.Value6) -> [a] -> STD.Value6
convertValue0To0List _ [] = STD.NilV6
convertValue0To0List fa (a : as) = STD.ConsV6 (fa a) (convertValue0To0List fa as)

convertValue0To0Pair :: (a -> STD.Value6) -> (b -> STD.Value6) -> (a, b) -> STD.Value6
convertValue0To0Pair fa fb (a, b) = STD.PairV6 (fa a) (fb b)

createValueConversionFunction0 :: (MonadState C0 m, MonadIO m, Quote m) => PG.Type -> m TH.Exp
createValueConversionFunction0 IntT = varE $ mkName "convertValue0To0Int"
createValueConversionFunction0 BoolT = varE $ mkName "convertValue0To0Bool"
createValueConversionFunction0 UnitT = varE $ mkName "convertValue0To0Unit"
createValueConversionFunction0 (PairT t0 t2) = appsE [varE $ mkName "convertValue0To0Pair", createValueConversionFunction0 t0, createValueConversionFunction0 t2]
createValueConversionFunction0 (PG.ListT t) = appsE [varE $ mkName "convertValue0To0List", createValueConversionFunction0 t]

convertValue0To0 :: (MonadState C0 m, MonadIO m, Quote m) => Value -> m TH.Exp
convertValue0To0 (LambdaV nm e) = lamE [varP $ mkName $ toVarName nm] $ convertExpr0To0 e
convertValue0To0 (IntV i) = litE $ integerL $ toInteger i
convertValue0To0 UnitV = conE $ mkName "()"
convertValue0To0 (BoolV b) = varE $ mkName $ show b
convertValue0To0 (PairV v1 v2) = appsE [conE $ mkName "(,)", convertValue0To0 v1, convertValue0To0 v2]
convertValue0To0 NilV = conE $ mkName "[]"
convertValue0To0 (ConsV v1 v2) = infixE (Just $ convertValue0To0 v1) (varE $ mkName ":") (Just $ convertValue0To0 v2)
convertValue0To0 (SuspendedV (Suspended e)) = convertExpr0To0 e

convertExpr0To0 :: (MonadState C0 m, MonadIO m, Quote m) => Expr -> m TH.Exp
convertExpr0To0 (Var varIdx) =
  appsE [conE $ mkName "Pure", varE $ mkName $ toVarName varIdx]
convertExpr0To0 (App e1 e2) =
  appsE [varE $ mkName "app0", convertExpr0To0 e1, convertExpr0To0 e2]
convertExpr0To0 (Let argIdx e1 e2) =
  appsE [conE $ mkName "let0", convertExpr0To0 e1, lamE [varP $ mkName $ toVarName argIdx] $ convertExpr0To0 e2]
convertExpr0To0 (OpCall effIdx opIdx e) = do
  tIdx <- gets c0TIdx
  appsE [varE $ mkName "opCall0", varE $ mkName $ toOpName tIdx effIdx opIdx, convertExpr0To0 e]
convertExpr0To0 (Handle h e) =
  appsE [varE $ mkName "sHandle0", convertHandler0To0 h, convertExpr0To0 e]
convertExpr0To0 (Lit v) =
  appsE [conE $ mkName "Pure", convertValue0To0 v]
convertExpr0To0 Hdl =
  appsE [conE $ mkName "Pure", varE $ mkName "hdl"]
convertExpr0To0 (Pair e1 e2) =
  appsE [varE $ mkName "pair0", convertExpr0To0 e1, convertExpr0To0 e2]
convertExpr0To0 (Cons e1 e2) =
  appsE [varE $ mkName "cons0", convertExpr0To0 e1, convertExpr0To0 e2]
convertExpr0To0 (UnOp uop e) =
  appsE [varE $ mkName "unOp0", convertUnOp0To0 uop, convertExpr0To0 e]
convertExpr0To0 (BinOp e1 bop e2) =
  appsE [varE $ mkName "binOp0", convertExpr0To0 e1, convertBinOp0To0 bop, convertExpr0To0 e2]
convertExpr0To0 (If e1 e2 e3) =
  appsE [varE $ mkName "if0", convertExpr0To0 e1, convertExpr0To0 e2, convertExpr0To0 e3]
convertExpr0To0 (Resume e) =
  appsE [varE $ mkName "app0", appsE [conE $ mkName "Pure", varE $ mkName "resume"], convertExpr0To0 e]

newtype P0
  = P0 TH.Exp
  deriving (Show)

instance Ppr P0 where
  ppr (P0 e) = ppr e

testFile0 :: FilePath
testFile0 = "test-generated/Final/ShallowToSmallTests0.hs"

testModule0 :: String
testModule0 = "Final.ShallowToSmallTests0"

createTestString0 :: Int -> PG.Type -> Expr -> IO String
createTestString0 testIdx ty e =
  flip evalStateT (C0 [] [] testIdx 0) $ do
    e0 <- convertExpr0To0 e

    effs <- gets c0Effs
    decs <- gets c0Where

    progTD <-
      sigD
        (mkName ("p" <> show testIdx))
        (conT $ mkName "ValueOrOp6")

    progD <-
      valD
        (varP $ mkName ("p" <> show testIdx))
        ( normalB $
            appsE
              [ varE $ mkName "NoOp6",
                appsE
                  [ createValueConversionFunction0 ty,
                    appsE [varE $ mkName "run0", return e0]
                  ]
              ]
        )
        (return <$> decs)

    return (show (ppr effs) <> "\n\n" <> show (ppr progTD) <> "\n" <> show (ppr progD) <> "\n\n")

testBatchInterpreter0 :: (MonadIO m, MonadInterpreter m) => [TypeAndExpr] -> m [QC.Result]
testBatchInterpreter0 tes = do
  -- Generate the test sample module and write it to file.
  s <- liftIO $ zipWithM (\(TypeAndExpr ty e) testIdx -> createTestString0 testIdx ty e) tes [0 ..]
  liftIO $ do
    fExists <- doesFileExist testFile0
    when fExists (removeFile testFile0)
    createDirectoryIfMissing True "test-generated/Final"
    writeFile
      testFile0
      ( "module "
          <> testModule0
          <> " where"
          <> "\n\n"
          <> "import Final.DTC"
          <> "\n"
          <> "import Final.ShallowToSmall"
          <> "\n"
          <> "import Final.ShallowToSmallTest (convertValue0To0Int, convertValue0To0Bool, convertValue0To0Pair, convertValue0To0List, convertValue0To0Unit)"
          <> "\n\n"
          <> concat s
      )

  -- Setup the interpreter by loading modules etc. Caching should already be done by only using
  -- runInterpreter in the outer testing level once.
  set
    [ languageExtensions
        := [ Language.Haskell.Interpreter.Extension.GADTs,
             Language.Haskell.Interpreter.Extension.GADTSyntax,
             Language.Haskell.Interpreter.Extension.TypeOperators
           ],
      searchPath := [".", "src", "test", "test-generated"]
    ]
  loadModules ["Final.ShallowToSmall", "Final.ShallowToSmallTest", testModule0]
  setImports ["Final.ShallowToSmall", testModule0]

  -- Run the many tests in this test set by using many 'interpret' calls.
  zipWithM
    ( \(TypeAndExpr _ e) testIdx -> do
        let v6 = STD.normalise6_9 $ convertToExpr6 e
        v0 <- interpret ("p" <> show testIdx) (as :: STD.ValueOrOp6)
        return (liftBool (v6 == v0))
    )
    tes
    [0 ..]

testMany0 :: Int -> Property
testMany0 n = ioProperty $ do
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
            tes <- liftIO $ replicateM sz $ generate arbitraryTypeAndShallowExpr
            testBatchInterpreter0 tes
        )
        batchSizes
