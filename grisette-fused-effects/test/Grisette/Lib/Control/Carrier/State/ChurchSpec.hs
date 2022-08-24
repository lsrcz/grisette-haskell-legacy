module Grisette.Lib.Control.Carrier.State.ChurchSpec where

import Control.Carrier.Lift
import Control.Carrier.State.Church
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.State.Church
import Grisette.Lib.Control.Carrier.State.Common
import Grisette.Lib.Control.Monad
import Grisette.TestUtils.SBool
import Test.Hspec

type R = StateC Int (LiftC (UnionMBase SBool)) SBool

spec :: Spec
spec = do
  describe "State.Church" $ do
    let r0 = mrgIf (SSBool "c") (return (2, SSBool "a")) (return (0, SSBool "b"))
    let r2 = mrgReturn (4, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    it "Mergeable for State.Church" $ do
      let s1 = sm (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState (curry mrgReturn) 0 s1) `shouldBe` r0
      runM (runState (curry mrgReturn) 2 s1) `shouldBe` r2
    it "Mergeable1 for State.Church" $ do
      let s1 = sm1 (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState (curry mrgReturn) 0 s1) `shouldBe` r0
      runM (runState (curry mrgReturn) 2 s1) `shouldBe` r2
    it "SimpleMergeable for State.Church" $ do
      let s1 = ss (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState (curry mrgReturn) 0 s1) `shouldBe` r0
      runM (runState (curry mrgReturn) 2 s1) `shouldBe` r2
    it "SimpleMergeable1 for State.Church" $ do
      let s1 = ss1 (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState (curry mrgReturn) 0 s1) `shouldBe` r0
      runM (runState (curry mrgReturn) 2 s1) `shouldBe` r2
    it "UnionLike for State.Church" $ do
      let s1 = su (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState (curry mrgReturn) 0 s1) `shouldBe` r0
      runM (runState (curry mrgReturn) 2 s1) `shouldBe` r2
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState (curry mrgReturn) 0 s1') `shouldBe` r0
      runM (runState (curry mrgReturn) 2 s1') `shouldBe` r2
      runM (runState (curry mrgReturn) 0 $ merge s1') `shouldBe` r0
      runM (runState (curry mrgReturn) 2 $ merge s1') `shouldBe` r2
      runM (runState (curry mrgReturn) 0 (mrgSingle (SSBool "a") :: R)) `shouldBe` mrgReturn (0, SSBool "a")
      runM (runState (curry mrgReturn) 0 (single (SSBool "a") :: R)) `shouldBe` mrgReturn (0, SSBool "a")
    it "mrgRunState" $ do
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (mrgRunState (curry mrgReturn) 0 s1') `shouldBe` r0
      runM (mrgRunState (curry mrgReturn) 2 s1') `shouldBe` r2
    it "mrgExecState" $ do
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (mrgExecState 0 s1') `shouldBe` mrgIf (SSBool "c") (return 2) (return 0)
      runM (mrgExecState 2 s1') `shouldBe` mrgReturn 4
    it "mrgEvalState" $ do
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (mrgEvalState 0 s1') `shouldBe` mrgIf (SSBool "c") (return $ SSBool "a") (return $ SSBool "b")
      runM (mrgEvalState 2 s1') `shouldBe` mrgIf (SSBool "c") (return $ SSBool "a") (return $ SSBool "b")
