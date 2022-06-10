module Grisette.Lib.Control.Effect.ReaderSpec where


import Control.Carrier.Lift
import Control.Carrier.Reader
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.Reader ()
import Grisette.Lib.Control.Effect.Reader
import Grisette.TestUtils.SBool
import Test.Hspec

spec :: Spec
spec = do
  describe "Reader effect functions should work" $ do
    let r1 = mrgAsk :: ReaderC Int (LiftC (UnionMBase SBool)) Int
    let r2 = mrgAsks (+1) :: ReaderC Int (LiftC (UnionMBase SBool)) Int
    let r3 = mrgLocal (+(1 :: Int)) mrgAsk :: ReaderC Int (LiftC (UnionMBase SBool)) Int
    it "mrgAsk should work" $ do
      runM (runReader 0 r1) `shouldBe` mrgReturn 0
    it "mrgAsks should work" $ do
      runM (runReader 0 r2) `shouldBe` mrgReturn 1
    it "mrgLocal should work" $ do
      runM (runReader 0 r3) `shouldBe` mrgReturn 1
      runM (runReader 0 $ r3 >> r1) `shouldBe` mrgReturn 0
