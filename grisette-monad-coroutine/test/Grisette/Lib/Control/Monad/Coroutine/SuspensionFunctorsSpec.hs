{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Grisette.Lib.Control.Monad.Coroutine.SuspensionFunctorsSpec where

import Control.Monad.Coroutine.SuspensionFunctors
import Grisette.Core.Data.Class.Mergeable
import Grisette.Lib.Control.Monad.Coroutine.SuspensionFunctors ()
import Grisette.TestUtils.Mergeable
import Grisette.TestUtils.SBool
import Test.Hspec
import Test.Hspec.QuickCheck

spec :: Spec
spec = do
  describe "Mergeable for suspension functors" $ do
    prop "Mergeable for Yield Integer Integer should work" $ \(x :: Integer, y :: Integer) -> do
      testMergeableSimpleEquivClass'
        (\(Yield a b) -> (a, b))
        (Yield x y)
        [DynamicSortedIdx x, DynamicSortedIdx y]
        [(SSBool "a", Yield x y, Yield x y, Yield x y)]
    it "Mergeable for Yield SBool SBool should work" $ do
      testMergeableSimpleEquivClass'
        (\(Yield a b) -> (a, b))
        (Yield (SSBool "a") (SSBool "b"))
        []
        [ ( SSBool "a",
            Yield (SSBool "b") (SSBool "c"),
            Yield (SSBool "d") (SSBool "e"),
            Yield (ITE (SSBool "a") (SSBool "b") (SSBool "d")) (ITE (SSBool "a") (SSBool "c") (SSBool "e"))
          )
        ]
    it "Mergeable for Await SBool SBool should work" $ do
      let SimpleStrategy s = mergingStrategy :: MergingStrategy SBool (Await SBool SBool)
      let a1 = Await Not
      let a2 = Await (And (SSBool "a"))
      let Await a3 = s (SSBool "b") a1 a2
      a3 (SSBool "c") `shouldBe` ITE (SSBool "b") (Not (SSBool "c")) (And (SSBool "a") (SSBool "c"))
    it "Mergeable for Request SBool SBool SBool should work" $ do
      let SimpleStrategy s = mergingStrategy :: MergingStrategy SBool (Request SBool SBool SBool)
      let a1 = Request (SSBool "a") Not
      let a2 = Request (SSBool "b") (And (SSBool "c"))
      let Request v3 a3 = s (SSBool "d") a1 a2
      v3 `shouldBe` ITE (SSBool "d") (SSBool "a") (SSBool "b")
      a3 (SSBool "e") `shouldBe` ITE (SSBool "d") (Not (SSBool "e")) (And (SSBool "c") (SSBool "e"))
