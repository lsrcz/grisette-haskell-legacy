module Grisette.Lib.Control.Effect.ThrowSpec where

import Control.Carrier.Error.Either
import Control.Carrier.Lift
import Grisette.Core hiding (mrgThrowError)
import Grisette.Lib.Control.Carrier.Error.Either ()
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Effect.Throw
import Grisette.TestUtils.SBool
import Test.Hspec

spec :: Spec
spec = do
  describe "Throw effect functions should work" $ do
    it "mrgThrowError should work" $ do
      let e1 = mrgThrowError (1 :: Int) :: ErrorC Int (LiftC (UnionMBase SBool)) Int
      runM (runError e1) `shouldBe` mrgReturn (Left 1)
    it "mrgLiftEither should work" $ do
      let e1 = mrgLiftEither (Left (1 :: Int)) :: ErrorC Int (LiftC (UnionMBase SBool)) Int
      let e2 = mrgLiftEither (Right 1 :: Either Int Int) :: ErrorC Int (LiftC (UnionMBase SBool)) Int
      runM (runError e1) `shouldBe` mrgReturn (Left 1)
      runM (runError e2) `shouldBe` mrgReturn (Right 1)
