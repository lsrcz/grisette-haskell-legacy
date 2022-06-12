module Grisette.Lib.Control.Carrier.Reader.ReaderSpec where

import Test.Hspec
import Grisette.Core
import Grisette.TestUtils.SBool
import Control.Carrier.Lift
import Control.Carrier.Reader
import Grisette.Lib.Control.Carrier.Reader.Common
import Grisette.Lib.Control.Carrier.Reader
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Monad

type M a = ReaderC Int (LiftC (UnionMBase SBool)) a
type R = M Int
type RB = M SBool

spec :: Spec
spec = do
  describe "Reader" $ do
    it "Mergeable for Reader" $ do
      runM (runReader 0 (rm (SSBool "c") (+1) (+2) :: R)) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (runReader 0 (rm (SSBool "c") (+1) (+1) :: R)) `shouldBe`
        mrgReturn 1
    it "Mergeable1 for Reader" $ do
      runM (runReader 0 (rm1 (SSBool "c") (+1) (+2) :: R)) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (runReader 0 (rm1 (SSBool "c") (+1) (+1) :: R)) `shouldBe`
        mrgReturn 1
    it "SimpleMergeable for Reader" $ do
      runM (runReader 0 (rs (SSBool "c") (+1) (+2) :: R)) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (runReader 0 (rs (SSBool "c") (+1) (+1) :: R)) `shouldBe`
        mrgReturn 1
    it "SimpleMergeable1 for Reader" $ do
      runM (runReader 0 (rs (SSBool "c") (const $ SSBool "a") (const $ SSBool "b") :: RB)) `shouldBe`
        mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    it "UnionLike for Reader" $ do
      runM (runReader 0 (ru (SSBool "c") (+1) (+2) :: R)) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (runReader 0 (ru (SSBool "c") (+1) (+1) :: R)) `shouldBe`
        mrgReturn 1
      runM (runReader 0 (ru' (SSBool "c") (+1) (+2) :: R)) `shouldBe`
        unionIf (SSBool "c") (return 1) (return 2)
      runM (runReader 0 (ru' (SSBool "c") (+1) (+1) :: R)) `shouldBe`
        unionIf (SSBool "c") (return 1) (return 1)
      runM (runReader 0 (mrgSingle 1 :: R)) `shouldBe` mrgReturn 1
      runM (runReader 0 (single 1 :: R)) `shouldBe` single 1
      runM (runReader 0 (merge $ ru' (SSBool "c") (+1) (+2) :: R)) `shouldBe`
        mrgIf (SSBool "c") (return 1) (return 2)
      runM (runReader 0 (merge $ ru' (SSBool "c") (+1) (+1) :: R)) `shouldBe`
        mrgReturn 1
      runM (runReader 0 (r (+1) :: R)) `shouldBe` single 1
    it "mrgRunReader" $ do
      runM (mrgRunReader 0 (r (+1) :: R)) `shouldBe` mrgReturn 1
      runM (mrgRunReader 0 (single 1 :: R)) `shouldBe` mrgReturn 1
