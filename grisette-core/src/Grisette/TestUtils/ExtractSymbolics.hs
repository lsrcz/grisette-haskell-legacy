{-# LANGUAGE FlexibleContexts #-}

module Grisette.TestUtils.ExtractSymbolics where

import qualified Data.HashSet as S
import Grisette.Core.Data.Class.ExtractSymbolics
import Grisette.TestUtils.SBool
import Test.Hspec

concreteExtractSymbolicsOkProp :: (HasCallStack, ExtractSymbolics (S.HashSet Symbol) a) => (a, a) -> Expectation
concreteExtractSymbolicsOkProp x = extractSymbolics x `shouldBe` (S.empty :: S.HashSet Symbol)
