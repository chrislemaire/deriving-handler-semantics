module Main
  ( module Test.Tasty,
    module Test.QuickCheck,
    module Final.ProgramGen,
    module Final.SmallToDeepTest,
    module Language.Haskell.TH,
    main,
  )
where

import Final.ProgramGen hiding (ListT, Type, VarT, Match)
import Final.ProgramGenTest
import Final.ScopedToSmallTest
import Final.ShallowToSmallTest
import Final.SmallToDeepTest
import Final.Writing.DanvySimpleTest
import Final.Writing.VeselySimpleTest
import Language.Haskell.TH
import Test.QuickCheck
import Test.Tasty

main :: IO ()
main = defaultMain mainTestGroup

mainTestGroup :: TestTree
mainTestGroup =
  testGroup
    "Main"
    [ Final.Writing.VeselySimpleTest.tests,
      Final.Writing.DanvySimpleTest.tests,
      Final.SmallToDeepTest.tests,
      Final.ShallowToSmallTest.tests,
      Final.ProgramGenTest.tests,
      Final.ScopedToSmallTest.tests
    ]

emptyTestGroup :: TestTree
emptyTestGroup = testGroup "empty" []
