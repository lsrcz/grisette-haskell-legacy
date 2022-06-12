{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.TestUtils.Mergeable where

import Grisette.Core.Data.Class.Mergeable
import Grisette.TestUtils.SBool
import Test.Hspec

testMergeableSimpleEquivClass ::
  (HasCallStack, Mergeable SBool x, Show x, Eq x) => x -> [DynamicOrderedIdx] -> [(SBool, x, x, x)] -> Expectation
testMergeableSimpleEquivClass x idxs cases = do
  let (idxsT, s) = resolveStrategy @SBool mergeStrategy x
  case s of
    SimpleStrategy m -> do
      idxsT `shouldBe` idxs
      go cases
      where
        go [] = return ()
        go ((c, t, f, r) : xs) = do
          fst (resolveStrategy @SBool mergeStrategy t) `shouldBe` idxs
          fst (resolveStrategy @SBool mergeStrategy f) `shouldBe` idxs
          fst (resolveStrategy @SBool mergeStrategy r) `shouldBe` idxs
          m c t f `shouldBe` r
          go xs
    _ -> expectationFailure $ "Bad strategy type for " ++ show x

testMergeableSimpleEquivClass' ::
  (HasCallStack, Mergeable SBool x, Show y, Eq y) => (x -> y) -> x -> [DynamicOrderedIdx] -> [(SBool, x, x, x)] -> Expectation
testMergeableSimpleEquivClass' vis x idxs cases = do
  let (idxsT, s) = resolveStrategy @SBool mergeStrategy x
  case s of
    SimpleStrategy m -> do
      idxsT `shouldBe` idxs
      go cases
      where
        go [] = return ()
        go ((c, t, f, r) : xs) = do
          fst (resolveStrategy @SBool mergeStrategy t) `shouldBe` idxs
          fst (resolveStrategy @SBool mergeStrategy f) `shouldBe` idxs
          fst (resolveStrategy @SBool mergeStrategy r) `shouldBe` idxs
          vis (m c t f) `shouldBe` vis r
          go xs
    _ -> expectationFailure $ "Bad strategy type for " ++ show (vis x)
