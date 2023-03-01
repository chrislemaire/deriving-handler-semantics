{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Final.TestUtil where

import Control.Monad.State (StateT (..), evalStateT, runStateT)
import Control.Monad.Trans
import Data.Char (isDigit)
import Test.QuickCheck (Property, forAll, withMaxSuccess)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.GenT
import Test.Tasty (TestTree)
import Test.Tasty.ExpectedFailure (ignoreTest)

runLongTests :: Bool
runLongTests = True

disableLongTests :: TestTree -> TestTree
disableLongTests = if runLongTests then id else ignoreTest

---------------------------------------------------------------
---- Program generator data type and instances
---------------------------------------------------------------
type MGen = StateT Int (GenT Maybe)

instance MonadGen MGen where
  liftGen = lift . liftGen
  variant n st = StateT (variant n . runStateT st)
  sized f = StateT (\s -> sized (\i -> runStateT (f i) s))
  resize n st = StateT (resize n . runStateT st)
  choose p = StateT (\s -> (,s) <$> choose p)

evalMGen :: MGen a -> Gen a
evalMGen st = do
  may <- runGenT $ evalStateT st 0
  case may of
    Nothing -> error ""
    Just v -> return v

-- A generator nested with maybes.
-- The outer maybe represents a type-based error when generating expressions,
--    making it completely impossible to generate expressions with this generator.
-- The inner maybe represents a 'runtime' generator error that can be re-tried.
type MMGen a = Maybe (MGen a)

-----------------------------------------------------
---- Helper functions for generating MGens and MMGens
-----------------------------------------------------
oneOfFail :: [MGen a] -> MGen a
oneOfFail l = do
  may <- oneofMay l
  case may of
    Nothing -> lift $ lift Nothing
    Just a -> return a

frequencyM :: [(Int, MMGen a)] -> MGen a
frequencyM fqs = case fqs' of
  [] -> lift $ lift Nothing
  _ -> frequency fqs'
  where
    fqs' = do
      (fq, may) <- fqs
      maybe [] ((: []) . (fq,)) may

frequencyMM :: [(Int, MMGen a)] -> MMGen a
frequencyMM fqs = case fqs' of
  [] -> Nothing
  _ -> Just $ frequency fqs'
  where
    fqs' = do
      (fq, may) <- fqs
      maybe [] ((: []) . (fq,)) may

---------------------------------------------------------------
---- Utility functions
---------------------------------------------------------------
firstJusts :: [Maybe a] -> Maybe a
firstJusts [] = Nothing
firstJusts (Nothing : xs) = firstJusts xs
firstJusts (j : _) = j

---------------------------------------------------------------
---- Property to test
---------------------------------------------------------------
programRunsTheSameProperty ::
  (Show e1, Eq v) =>
  (e1 -> e2) ->
  (e1 -> v) ->
  (e2 -> v) ->
  Gen e1 ->
  Property
programRunsTheSameProperty convert run1 run2 ge1 =
  withMaxSuccess 10000 $
    forAll ge1 $
      \e1 -> run1 e1 == run2 (convert e1)

---------------------------------------------------------------
---- Utilities for writing conversions
---------------------------------------------------------------
toTyVarName :: Int -> String
toTyVarName idx = "x" <> show idx

toVarName :: Int -> String
toVarName idx = "v" <> show idx

toEffName :: Int -> Int -> String
toEffName tIdx effIdx = "T" <> show tIdx <> "Eff" <> show effIdx

toScopeEffName :: Int -> Int -> String
toScopeEffName tIdx effIdx = "T" <> show tIdx <> "Scp" <> show effIdx

toTypeName :: Int -> Int -> String
toTypeName tIdx effIdx = "T" <> show tIdx <> "F" <> show effIdx

toUnTypeName :: Int -> Int -> String
toUnTypeName tIdx effIdx = "unT" <> show tIdx <> "F" <> show effIdx

toOpName :: Int -> Int -> Int -> String
toOpName tIdx effIdx opIdx = "T" <> show tIdx <> "Eff" <> show effIdx <> "Op" <> show opIdx

toScopeName :: Int -> Int -> Int -> String
toScopeName tIdx effIdx scopeIdx = "T" <> show tIdx <> "Eff" <> show effIdx <> "Scope" <> show scopeIdx

fromOpName :: String -> (Int, Int)
fromOpName opNm = (read $ takeWhile isDigit $ drop 3 opNm, read $ reverse $ takeWhile isDigit $ reverse opNm)
