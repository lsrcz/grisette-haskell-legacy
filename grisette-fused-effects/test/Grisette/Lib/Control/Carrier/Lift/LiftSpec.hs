module Grisette.Lib.Control.Carrier.Lift.LiftSpec where

import Test.Hspec
import Grisette.Core
import Grisette.TestUtils.SBool
import Control.Carrier.Lift
import Grisette.Lib.Control.Carrier.Lift
import Grisette.Lib.Control.Carrier.Lift.Common
import Grisette.Lib.Control.Monad

type M a = LiftC (UnionMBase SBool) a
type R = M Int
type RB = M SBool

spec :: Spec
spec = do
  describe "Lift" $ do
    it "Mergeable for Lift" $ do
      runM (lm (SSBool "c") 1 2 :: R) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (lm (SSBool "c") 1 1 :: R) `shouldBe`
        mrgReturn 1
    it "Mergeable1 for Lift" $ do
      runM (lm1 (SSBool "c") 1 2 :: R) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (lm1 (SSBool "c") 1 1 :: R) `shouldBe`
        mrgReturn 1
    it "SimpleMergeable for Lift" $ do
      runM (ls (SSBool "c") 1 2 :: R) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (ls (SSBool "c") 1 1 :: R) `shouldBe`
        mrgReturn 1
    it "SimpleMergeable1 for Lift" $ do
      runM (ls (SSBool "c") (SSBool "a") (SSBool "b") :: RB) `shouldBe`
        mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    it "UnionLike for Lift" $ do
      runM (lu (SSBool "c") 1 2 :: R) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (lu (SSBool "c") 1 1 :: R) `shouldBe`
        mrgReturn 1
      runM (lu' (SSBool "c") 1 2 :: R) `shouldBe`
        unionIf (SSBool "c") (return 1) (return 2)
      runM (lu' (SSBool "c") 1 1 :: R) `shouldBe`
        unionIf (SSBool "c") (return 1) (return 1)
      runM (mrgSingle 1 :: R) `shouldBe` mrgReturn 1
      runM (single 1 :: R) `shouldBe` single 1
      runM (merge $ lu' (SSBool "c") 1 2 :: R) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (merge $ lu' (SSBool "c") 1 1 :: R) `shouldBe`
        mrgReturn 1
      runM (l 1 :: R) `shouldBe` single 1
    it "mrgRunM" $ do
      mrgRunM (l 1 :: R) `shouldBe` mrgReturn 1
      mrgRunM (single 1 :: R) `shouldBe` mrgReturn 1
