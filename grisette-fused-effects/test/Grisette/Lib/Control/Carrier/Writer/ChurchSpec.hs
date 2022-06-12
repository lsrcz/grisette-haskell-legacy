module Grisette.Lib.Control.Carrier.Writer.ChurchSpec where

import Control.Carrier.Lift
import Control.Carrier.Writer.Church
import Data.Monoid
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.Writer.Church
import Grisette.Lib.Control.Carrier.Writer.Common
import Grisette.Lib.Control.Monad
import Grisette.TestUtils.SBool
import Test.Hspec

type R = WriterC (Sum Int) (LiftC (UnionMBase SBool)) SBool

spec :: Spec
spec = do
  describe "Writer.Church" $ do
    it "Mergeable for Writer.Church" $ do
      runM (runWriter (curry mrgReturn) (wm (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (curry mrgReturn) (wm (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "Mergeable1 for Writer.Church" $ do
      runM (runWriter (curry mrgReturn) (wm1 (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (curry mrgReturn) (wm1 (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "SimpleMergeable for Writer.Church" $ do
      runM (runWriter (curry mrgReturn) (ws (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (curry mrgReturn) (ws (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "SimpleMergeable1 for Writer.Church" $ do
      runM (runWriter (curry mrgReturn) (ws1 (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (curry mrgReturn) (ws1 (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
    it "UnionLike for Writer.Church" $ do
      runM (runWriter (curry mrgReturn) (wu (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgReturn (Sum 10, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
      runM (runWriter (curry mrgReturn) (wu (SSBool "c") 10 (SSBool "a") 20 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (mrgReturn (Sum 10, SSBool "a")) (mrgReturn (Sum 20, SSBool "b"))
      runM (runWriter (curry mrgReturn) (merge $ single (SSBool "a") :: R)) `shouldBe` mrgSingle (Sum 0, SSBool "a")
      runM (runWriter (curry return) (merge $ single (SSBool "a") :: R)) `shouldBe` single (Sum 0, SSBool "a")
      runM (runWriter (curry mrgReturn) (mrgSingle (SSBool "a") :: R)) `shouldBe` mrgSingle (Sum 0, SSBool "a")
      runM (runWriter (curry return) (mrgSingle (SSBool "a") :: R)) `shouldBe` single (Sum 0, SSBool "a")
      runM (runWriter (curry mrgReturn) (single (SSBool "a") :: R)) `shouldBe` mrgSingle (Sum 0, SSBool "a")
      runM (runWriter (curry return) (single (SSBool "a") :: R)) `shouldBe` single (Sum 0, SSBool "a")
      runM (runWriter (curry mrgReturn) (wu' (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (single (Sum 10, SSBool "a")) (single (Sum 10, SSBool "b"))
      runM (runWriter (curry return) (wu' (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` unionIf (SSBool "c") (single (Sum 10, SSBool "a")) (single (Sum 10, SSBool "b"))
    it "mrgRunWriter" $ do
      runM (mrgRunWriter (curry return) (w 1 (SSBool "a") :: R)) `shouldBe` mrgReturn (Sum 1, SSBool "a")
      runM (mrgRunWriter (curry return) (wu' (SSBool "c") 10 (SSBool "a") 10 (SSBool "b") :: R))
        `shouldBe` mrgIf (SSBool "c") (single (Sum 10, SSBool "a")) (single (Sum 10, SSBool "b"))
    it "mrgExecWriter" $ do
      runM (mrgExecWriter (w 1 (SSBool "a") :: R)) `shouldBe` mrgReturn (Sum 1)
