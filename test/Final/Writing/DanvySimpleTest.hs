module Final.Writing.DanvySimpleTest where

import Control.Monad.State
import Data.Maybe (maybeToList)
import Final.TestUtil
import Final.Writing.DanvySimple
import Test.QuickCheck (withMaxSuccess)
import Test.QuickCheck.Gen (Gen, chooseInt)
import Test.QuickCheck.GenT
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty)

tests :: TestTree
tests =
  testGroup
    "Simple Danvy language"
    [ testGroup
        "Generated"
        [ testProperty "Equivalence of normalise0 and normalise1" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise1 (resize 1000 arbitraryExpr),
          testProperty "Equivalence of normalise0 and normalise2" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise2 (resize 1000 arbitraryExpr),
          testProperty "Equivalence of normalise0 and normalise3" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise3 (resize 1000 arbitraryExpr),
          testProperty "Equivalence of normalise0 and normalise4" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise4 (resize 1000 arbitraryExpr),
          testProperty "Equivalence of normalise0 and normalise5" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise5 (resize 1000 arbitraryExpr),
          testProperty "Equivalence of normalise0 and normalise6" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise6 (resize 1000 arbitraryExpr),
          testProperty "Equivalence of normalise0 and normalise7" $
            withMaxSuccess 10000 $
              programRunsTheSameProperty id normalise0 normalise7 (resize 1000 arbitraryExpr)
        ]
    ]

-----------------------------------------------------
---- Generators and arbitraries
-----------------------------------------------------
varsOfType :: [Type] -> Type -> [(Type, String)]
varsOfType nv ty =
  filter (\(ty', _) -> ty == ty') $
    zip nv ["v" <> show i | i <- [0 ..]]

genType :: Bool -> MGen Type
genType eqOnly = sized arb
  where
    arb :: Int -> MGen Type
    arb 0 = return IntT
    arb n =
      frequency $
        (1, return IntT) :
          [(2, FunT <$> arb (n `div` 6) <*> arb (n `div` 4)) | not eqOnly]

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
      (FunT argT retT) ->
        return $
          LambdaV ("v" <> show (length nv))
            <$> arbExpr (nv <> [argT]) tVars retT 0

    arb :: Type -> [MGen Expr]
    arb ty = maybeToList (fmap Lit <$> arbV ty) <> ((\(_, idx) -> return (Var idx)) <$> varsOfType nv ty)

arbExpr :: [Type] -> Int -> Type -> Int -> MGen Expr
arbExpr nv tVars ty 0 =
  frequencyM $
    [(1, genLitValue nv tVars ty)]
      <> ((\(_, idx) -> (1, Just $ return (Var idx))) <$> varsOfType nv ty)
arbExpr nv tVars ty n =
  frequencyM $
    ((\(_, idx) -> (20, Just $ return (Var idx))) <$> varsOfType nv ty)
      -- app
      <> [ ( 2,
             Just $ do
               argT <- genType False
               funE <- arbExpr nv tVars (FunT argT ty) (n `div` 4)
               argE <- arbExpr nv tVars argT (n `div` 4)
               return $ App funE argE
           )
         ]
      -- let
      <> [ ( 5,
             Just $ do
               argT <- genType False
               argE <- arbExpr nv tVars argT (n `div` 4)
               bodyE <- arbExpr (nv <> [argT]) tVars ty (n `div` 4)
               return $ Let ("v" <> show (length nv)) argE bodyE
           )
         ]
      -- literals
      <> [(5, genLitValue nv tVars ty)]
      -- lambda-expressions
      <> [ ( 7,
             withFunT
               ( \argT retT -> do
                   bodyE <- arbExpr (nv <> [argT]) tVars retT (n `div` 2)
                   return $ Lit $ LambdaV ("v" <> show (length nv)) bodyE
               )
           )
         ]
      -- bin-ops
      <> [ ( 5,
             withIntT $ do
               binOp <- elements [Add, Mul]
               e1 <- arbExpr nv tVars IntT (n `div` 4)
               e2 <- arbExpr nv tVars IntT (n `div` 4)
               return $ BinOp e1 binOp e2
           )
         ]
  where
    withFunT :: (Type -> Type -> MGen Expr) -> Maybe (MGen Expr)
    withFunT f = case ty of
      FunT argT retT -> Just $ f argT retT
      _ -> Nothing

    withIntT :: MGen Expr -> Maybe (MGen Expr)
    withIntT g = case ty of
      IntT -> Just g
      _ -> Nothing

arbitraryType :: Gen Type
arbitraryType = do
  may <- runGenT $ flip evalStateT 0 $ genType True
  maybe arbitraryType return may

arbitraryExpr :: Gen Expr
arbitraryExpr = do
  ty <- arbitraryType
  go ty
  where
    go :: Type -> Gen Expr
    go ty = do
      may <- runGenT $ flip evalStateT 0 $ sized (arbExpr [] 0 ty)
      maybe (go ty) return may
