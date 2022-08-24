module Grisette.Lib.Control.Carrier.Throw.EitherSpec where

import Control.Carrier.Lift
import Control.Carrier.Throw.Either
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.Throw.Common
import Grisette.Lib.Control.Carrier.Throw.Either
import Grisette.Lib.Control.Monad
import Grisette.TestUtils.SBool
import Test.Hspec

type M a = ThrowC Int (LiftC (UnionMBase SBool)) a

type R = M Int

type RB = M SBool

spec :: Spec
spec = do
  describe "Throw.Either" $ do
    it "Mergeable for Throw.Either" $ do
      runM (runThrow (em (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runThrow (em (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runThrow (em (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runThrow (em (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runThrow (em (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "Mergeable1 for Throw.Either" $ do
      runM (runThrow (em1 (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runThrow (em1 (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runThrow (em1 (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runThrow (em1 (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runThrow (em1 (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "SimpleMergeable for Throw.Either" $ do
      runM (runThrow (es (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runThrow (es (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runThrow (es (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runThrow (es (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runThrow (es (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "SimpleMergeable1 for Throw.Either" $ do
      runM (runThrow (es1 (SSBool "c") (Left (1 :: Int)) (Left 1) :: RB))
        `shouldBe` mrgReturn (Left 1)
      runM (runThrow (es1 (SSBool "c") (Left (1 :: Int)) (Left 2) :: RB))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runThrow (es1 (SSBool "c") (Left (1 :: Int)) (Right $ SSBool "a") :: RB))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right $ SSBool "a"))
      runM (runThrow (es1 (SSBool "c") (Right $ SSBool "a" :: Either Int SBool) (Right $ SSBool "b") :: RB))
        `shouldBe` mrgReturn (Right $ ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    it "UnionLike for Throw.Either" $ do
      runM (runThrow (eu (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runThrow (eu (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runThrow (eu (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runThrow (eu (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runThrow (eu (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
      runM (runThrow (eu' (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Left 1)) (return (Left 1))
      runM (runThrow (eu' (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runThrow (eu' (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runThrow (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Right 1)) (return (Right 1))
      runM (runThrow (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Right 1)) (return (Right 2))
      runM (runThrow (single 1 :: R)) `shouldBe` return (return 1)
      runM (runThrow (mrgSingle 1 :: R)) `shouldBe` mrgReturn (return 1)
      runM (runThrow (merge $ single 1 :: R)) `shouldBe` mrgReturn (return 1)
    it "mrgRunThrow" $ do
      runM (mrgRunThrow (eu' (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (mrgRunThrow (eu' (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (mrgRunThrow (eu' (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (mrgRunThrow (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (mrgRunThrow (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
