{-# LANGUAGE TupleSections #-}

module Final.ProgramGenTest (tests) where

import Final.ProgramGen
import Final.TestUtil
import Test.Tasty
import Test.Tasty.QuickCheck

tests :: TestTree
tests =
  testGroup
    "Small to Deep conversion"
    [ testProperty
        "Replace TVar reverses insert TVar"
        insertTVarProperty
    ]

insertTVarProperty :: Property
insertTVarProperty =
  withMaxSuccess 100000
    $ forAll
      ( do
          ty <- arbitraryType True
          evalMGen $ (ty,) <$> insertTVar 0 ty Nothing
      )
    $ \(ty, (ty', vtm)) ->
      (\vt -> replaceTVar 0 vt ty' == ty) <$> vtm
