{-# LANGUAGE FlexibleContexts #-}
module Grisette.TestUtils.Evaluate where

import Test.Hspec
import Grisette.Core.Data.Class.Evaluate
import qualified Data.HashMap.Strict as M
import Grisette.TestUtils.SBool

concreteEvaluateOkProp :: (HasCallStack, Evaluate (M.HashMap Symbol Bool) a, Show a, Eq a) => a -> Expectation
concreteEvaluateOkProp x = evaluate True (M.empty :: M.HashMap Symbol Bool) x `shouldBe` x
