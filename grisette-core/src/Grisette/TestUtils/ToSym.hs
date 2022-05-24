module Grisette.TestUtils.ToSym where

import Grisette.Data.Class.ToSym
import Test.Hspec

toSymForConcreteOkProp :: (HasCallStack, ToSym v v, Show v, Eq v) => v -> Expectation
toSymForConcreteOkProp v = toSym v `shouldBe` v
