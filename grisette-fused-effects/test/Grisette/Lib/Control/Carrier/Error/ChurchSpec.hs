module Grisette.Lib.Control.Carrier.Error.ChurchSpec where

import Control.Carrier.Error.Church
import Control.Carrier.Lift
import Grisette.Lib.Control.Carrier.Error.Church
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Core
import Grisette.TestUtils.SBool
import Test.Hspec
import Grisette.Lib.Control.Carrier.Error.Common

type M a = ErrorC Int (LiftC (UnionMBase SBool)) a
type R = M Int
type RB = M SBool

spec :: Spec
spec = do
  describe "Error.Church" $ do
    it "Mergeable for Error.Church" $ do
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "Mergeable1 for Error.Church" $ do
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em1 (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em1 (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em1 (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em1 (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (em1 (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "SimpleMergeable for Error.Church" $ do
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "SimpleMergeable1 for Error.Church" $ do
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es1 (SSBool "c") (Left (1 :: Int)) (Left 1) :: RB))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es1 (SSBool "c") (Left (1 :: Int)) (Left 2) :: RB))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es1 (SSBool "c") (Left (1 :: Int)) (Right $ SSBool "a") :: RB))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right $ SSBool "a"))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (es1 (SSBool "c") (Right $ SSBool "a" :: Either Int SBool) (Right $ SSBool "b") :: RB))
        `shouldBe` mrgReturn (Right $ ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    it "UnionLike for Error.Church" $ do
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))

      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu' (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu' (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu' (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (single 1 :: R)) `shouldBe` mrgReturn (return 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (mrgSingle 1 :: R)) `shouldBe` mrgReturn (return 1)
      runM (runError (mrgReturn . Left) (mrgReturn . Right) (merge $ single 1 :: R)) `shouldBe` mrgReturn (return 1)
    it "mrgRunError" $ do
      runM (mrgRunError (return . Left) (return . Right) (eu' (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (mrgRunError (return . Left) (return . Right) (eu' (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (mrgRunError (return . Left) (return . Right) (eu' (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (mrgRunError (return . Left) (return . Right) (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (mrgRunError (return . Left) (return . Right) (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
