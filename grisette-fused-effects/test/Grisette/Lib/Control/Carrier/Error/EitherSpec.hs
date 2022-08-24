module Grisette.Lib.Control.Carrier.Error.EitherSpec where

import Control.Carrier.Error.Either
import Control.Carrier.Lift
import Grisette.Core
import Grisette.Lib.Control.Carrier.Error.Common
import Grisette.Lib.Control.Carrier.Error.Either
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Monad
import Grisette.TestUtils.SBool
import Test.Hspec

type M a = ErrorC Int (LiftC (UnionMBase SBool)) a

type R = M Int

type RB = M SBool

spec :: Spec
spec = do
  describe "Error.Either" $ do
    it "Mergeable for Error.Either" $ do
      runM (runError (em (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (em (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (em (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (em (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (em (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "Mergeable1 for Error.Either" $ do
      runM (runError (em1 (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (em1 (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (em1 (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (em1 (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (em1 (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "SimpleMergeable for Error.Either" $ do
      runM (runError (es (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (es (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (es (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (es (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (es (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
    it "SimpleMergeable1 for Error.Either" $ do
      runM (runError (es1 (SSBool "c") (Left (1 :: Int)) (Left 1) :: RB))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (es1 (SSBool "c") (Left (1 :: Int)) (Left 2) :: RB))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (es1 (SSBool "c") (Left (1 :: Int)) (Right $ SSBool "a") :: RB))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right $ SSBool "a"))
      runM (runError (es1 (SSBool "c") (Right $ SSBool "a" :: Either Int SBool) (Right $ SSBool "b") :: RB))
        `shouldBe` mrgReturn (Right $ ITE (SSBool "c") (SSBool "a") (SSBool "b"))
    it "UnionLike for Error.Either" $ do
      runM (runError (eu (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (runError (eu (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (eu (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (eu (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (runError (eu (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
      runM (runError (eu' (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Left 1)) (return (Left 1))
      runM (runError (eu' (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (runError (eu' (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (runError (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Right 1)) (return (Right 1))
      runM (runError (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` unionIf (SSBool "c") (return (Right 1)) (return (Right 2))
      runM (runError (single 1 :: R)) `shouldBe` return (return 1)
      runM (runError (mrgSingle 1 :: R)) `shouldBe` mrgReturn (return 1)
      runM (runError (merge $ single 1 :: R)) `shouldBe` mrgReturn (return 1)
    it "mrgRunError" $ do
      runM (mrgRunError (eu' (SSBool "c") (Left (1 :: Int)) (Left 1) :: R))
        `shouldBe` mrgReturn (Left 1)
      runM (mrgRunError (eu' (SSBool "c") (Left (1 :: Int)) (Left 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Left 2))
      runM (mrgRunError (eu' (SSBool "c") (Left (1 :: Int)) (Right 1) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Left 1)) (return (Right 1))
      runM (mrgRunError (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 1) :: R))
        `shouldBe` mrgReturn (Right 1)
      runM (mrgRunError (eu' (SSBool "c") (Right 1 :: Either Int Int) (Right 2) :: R))
        `shouldBe` mrgIf (SSBool "c") (return (Right 1)) (return (Right 2))
