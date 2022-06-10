module Grisette.Lib.Control.Effect.FreshSpec where

import Control.Carrier.Fresh.Strict
import Control.Carrier.Lift
import Grisette.Core
import Grisette.Lib.Control.Carrier.Fresh.Strict ()
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Effect.Fresh
import Test.Hspec
import Grisette.TestUtils.SBool

spec :: Spec
spec = do
  describe "Fresh effect functions should work" $ do
    it "mrgFresh should work" $ do
      let f1 = mrgFresh :: FreshC (LiftC (UnionMBase SBool)) Int
      runM (runFresh 0 f1) `shouldBe` mrgReturn (1, 0)
