module Grisette.Lib.Control.Carrier.State.StrictSpec where

import Control.Carrier.Lift
import Control.Carrier.State.Strict
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.State.Common
import Grisette.Lib.Control.Carrier.State.Strict
import Grisette.TestUtils.SBool
import Test.Hspec

type R = StateC Int (LiftC (UnionMBase SBool)) SBool

spec :: Spec
spec = do
  describe "State.Strict" $ do
    let r0 = mrgIf (SSBool "c") (return (2, SSBool "a")) (return (0, SSBool "b"))
    let r2 = mrgReturn (4, ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    let r0' = unionIf (SSBool "c") (return (2, SSBool "a")) (return (0, SSBool "b"))
    let r2' = unionIf (SSBool "c") (return (4, SSBool "a")) (return (4, SSBool "b"))
    it "Mergeable for State.Strict" $ do
      let s1 = sm (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState 0 s1) `shouldBe` r0
      runM (runState 2 s1) `shouldBe` r2
    it "Mergeable1 for State.Strict" $ do
      let s1 = sm1 (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState 0 s1) `shouldBe` r0
      runM (runState 2 s1) `shouldBe` r2
    it "SimpleMergeable for State.Strict" $ do
      let s1 = ss (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState 0 s1) `shouldBe` r0
      runM (runState 2 s1) `shouldBe` r2
    it "SimpleMergeable1 for State.Strict" $ do
      let s1 = ss1 (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState 0 s1) `shouldBe` r0
      runM (runState 2 s1) `shouldBe` r2
    it "UnionLike for State.Strict" $ do
      let s1 = su (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState 0 s1) `shouldBe` r0
      runM (runState 2 s1) `shouldBe` r2
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (runState 0 s1') `shouldBe` r0'
      runM (runState 2 s1') `shouldBe` r2'
      runM (runState 0 $ merge s1') `shouldBe` r0
      runM (runState 2 $ merge s1') `shouldBe` r2
      runM (runState 0 (mrgSingle (SSBool "a") :: R)) `shouldBe` mrgReturn (0, SSBool "a")
      runM (runState 0 (single (SSBool "a") :: R)) `shouldBe` return (0, SSBool "a")
    it "mrgRunState" $ do
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (mrgRunState 0 s1') `shouldBe` r0
      runM (mrgRunState 2 s1') `shouldBe` r2
    it "mrgExecState" $ do
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (mrgExecState 0 s1') `shouldBe` mrgIf (SSBool "c") (return 2) (return 0)
      runM (mrgExecState 2 s1') `shouldBe` mrgReturn 4
    it "mrgEvalState" $ do
      let s1' = su' (SSBool "c") (+ 2) (const $ SSBool "a") (* 2) (const $ SSBool "b") :: R
      runM (mrgEvalState 0 s1') `shouldBe` mrgIf (SSBool "c") (return $ SSBool "a") (return $ SSBool "b")
      runM (mrgEvalState 2 s1') `shouldBe` mrgIf (SSBool "c") (return $ SSBool "a") (return $ SSBool "b")
    
