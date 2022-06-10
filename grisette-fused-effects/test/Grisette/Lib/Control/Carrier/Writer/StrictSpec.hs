module Grisette.Lib.Control.Carrier.Writer.StrictSpec where

import Control.Carrier.Lift
import Control.Carrier.Writer.Strict
import Data.Monoid
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.Writer.Common
import Grisette.Lib.Control.Carrier.Writer.Strict
import Grisette.TestUtils.SBool
import Test.Hspec

type R = WriterC (Sum Int) (LiftC (UnionMBase SBool)) SBool

spec :: Spec
spec = do
  describe "Writer.Strict" $ do
    it "Mergeable for Writer.Strict" $ do
      runM (runWriter (wm (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (wm (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "Mergeable1 for Writer.Strict" $ do
      runM (runWriter (wm1 (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (wm1 (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "SimpleMergeable for Writer.Strict" $ do
      runM (runWriter (ws (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (ws (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "SimpleMergeable1 for Writer.Strict" $ do
      runM (runWriter (ws1 (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (ws1 (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "UnionLike for Writer.Strict" $ do
      runM (runWriter (wu (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (wu (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
      runM (runWriter (merge $ single (SSBool "a") :: R)) `shouldBe` mrgSingle (Sum 0, SSBool "a")
      runM (runWriter (mrgSingle (SSBool "a") :: R)) `shouldBe` mrgSingle (Sum 0, SSBool "a")
      runM (runWriter (single (SSBool "a") :: R)) `shouldBe` single (Sum 0, SSBool "a")
      runM (runWriter (wu' (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` unionIf (SSBool "c") (single (Sum 10, SSBool "a")) (single (Sum 10, SSBool "b"))
    it "mrgRunWriter" $ do
      runM (mrgRunWriter (w 1 (SSBool "a") :: R)) `shouldBe` mrgReturn (Sum 1, SSBool "a")
      runM (mrgRunWriter (wu' (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (single (Sum 10, SSBool "a")) (single (Sum 10, SSBool "b"))
    it "mrgExecWriter" $ do
      runM (mrgExecWriter (w 1 (SSBool "a") :: R)) `shouldBe` mrgReturn (Sum 1)
