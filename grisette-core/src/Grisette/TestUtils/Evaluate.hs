{-# LANGUAGE FlexibleContexts #-}

module Grisette.TestUtils.Evaluate where

import qualified Data.HashMap.Strict as M
import Grisette.Core.Data.Class.Evaluate
import Grisette.TestUtils.SBool
import Test.Hspec

concreteEvaluateOkProp :: (HasCallStack, Evaluate (M.HashMap Symbol Bool) a, Show a, Eq a) => a -> Expectation
concreteEvaluateOkProp x = evaluate True (M.empty :: M.HashMap Symbol Bool) x `shouldBe` x
