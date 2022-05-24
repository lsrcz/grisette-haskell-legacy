{-# LANGUAGE FlexibleContexts #-}

module Grisette.TestUtils.SEq where

import Grisette.Data.Class.Bool
import Grisette.TestUtils.SBool
import Test.Hspec

concreteSEqOkProp :: (HasCallStack, SEq SBool a, Eq a) => (a, a) -> Expectation
concreteSEqOkProp (i, j) = do
  i ==~ j `shouldBe` CBool (i == j)
  i /=~ j `shouldBe` CBool (i /= j)
