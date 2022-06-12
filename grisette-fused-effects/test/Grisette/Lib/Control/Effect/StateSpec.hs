{-# LANGUAGE TypeApplications #-}

module Grisette.Lib.Control.Effect.StateSpec where

import Control.Carrier.Lift
import Control.Carrier.State.Strict
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.State.Strict ()
import Grisette.Lib.Control.Monad
import Grisette.Lib.Control.Effect.State
import Grisette.TestUtils.SBool
import Test.Hspec

spec :: Spec
spec = do
  describe "State effect functions should work" $ do
    let s1 = mrgState (\a -> (a * 2 :: Int, a + 2)) :: StateC Int (LiftC (UnionMBase SBool)) Int
    let s2 = mrgState (\a -> (a + 2 :: Int, a * 2)) :: StateC Int (LiftC (UnionMBase SBool)) Int
    it "mrgState should work" $ do
      runM (runState 0 s1) `shouldBe` mrgReturn (0, 2)
      runM (runState 0 s2) `shouldBe` mrgReturn (2, 0)
      runM (runState 2 s1) `shouldBe` mrgReturn (4, 4)
      runM (runState 2 s2) `shouldBe` mrgReturn (4, 4)
      runM (runState 0 $ s1 >> s2) `shouldBe` mrgReturn (2, 0)
      runM (runState 2 $ s1 >> s2) `shouldBe` mrgReturn (6, 8)
      runM (runState 0 $ s2 >> s1) `shouldBe` mrgReturn (4, 4)
      runM (runState 2 $ s2 >> s1) `shouldBe` mrgReturn (8, 6)
    it "mrgGet should work" $ do
      runM (runState 0 $ s1 >> mrgGet @Int) `shouldBe` mrgReturn (0, 0)
      runM (runState 2 $ s1 >> mrgGet @Int) `shouldBe` mrgReturn (4, 4)
      runM (runState 0 $ s2 >> mrgGet @Int) `shouldBe` mrgReturn (2, 2)
      runM (runState 2 $ s2 >> mrgGet @Int) `shouldBe` mrgReturn (4, 4)
    it "mrgGets should work" $ do
      runM (runState 0 $ s1 >> mrgGets @Int (+ 1)) `shouldBe` mrgReturn (0, 1)
      runM (runState 2 $ s1 >> mrgGets @Int (+ 1)) `shouldBe` mrgReturn (4, 5)
      runM (runState 0 $ s2 >> mrgGets @Int (+ 1)) `shouldBe` mrgReturn (2, 3)
      runM (runState 2 $ s2 >> mrgGets @Int (+ 1)) `shouldBe` mrgReturn (4, 5)
    it "mrgPut should work" $ do
      runM (runState 0 $ s1 >> mrgPut @Int 1) `shouldBe` mrgReturn (1, ())
      runM (runState 2 $ s1 >> mrgPut @Int 1) `shouldBe` mrgReturn (1, ())
      runM (runState 0 $ mrgPut @Int 1 >> s1) `shouldBe` mrgReturn (2, 3)
      runM (runState 2 $ mrgPut @Int 1 >> s1) `shouldBe` mrgReturn (2, 3)
    it "mrgModify should work" $ do
      runM (runState 0 $ s1 >> mrgModify @Int (+ 1)) `shouldBe` mrgReturn (1, ())
      runM (runState 2 $ s1 >> mrgModify @Int (+ 1)) `shouldBe` mrgReturn (5, ())
      runM (runState 0 $ mrgModify @Int (+ 1) >> s1) `shouldBe` mrgReturn (2, 3)
      runM (runState 2 $ mrgModify @Int (+ 1) >> s1) `shouldBe` mrgReturn (6, 5)
    it "mrgModifyLazy should work" $ do
      runM (runState 0 $ s1 >> mrgModifyLazy @Int (+ 1)) `shouldBe` mrgReturn (1, ())
      runM (runState 2 $ s1 >> mrgModifyLazy @Int (+ 1)) `shouldBe` mrgReturn (5, ())
      runM (runState 0 $ mrgModifyLazy @Int (+ 1) >> s1) `shouldBe` mrgReturn (2, 3)
      runM (runState 2 $ mrgModifyLazy @Int (+ 1) >> s1) `shouldBe` mrgReturn (6, 5)
