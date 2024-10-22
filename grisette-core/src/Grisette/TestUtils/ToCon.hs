module Grisette.TestUtils.ToCon where

import Grisette.Core.Data.Class.ToCon
import Test.Hspec

toConForConcreteOkProp :: (HasCallStack, ToCon v v, Show v, Eq v) => v -> Expectation
toConForConcreteOkProp v = toCon v `shouldBe` Just v
