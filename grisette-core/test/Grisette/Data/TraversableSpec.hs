module Grisette.Data.TraversableSpec where

import Control.Monad.Except hiding (guard)
import Grisette.Control.Monad.Union
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Grisette.Data.Traversable
import Test.Hspec
import Grisette.TestUtils.SBool

spec :: Spec
spec = do
  describe "mrgTraverse" $
    it "mrgTraverse should work" $ do
      runExceptT
        ( mrgTraverse
            (\(c, d, x, y, z) -> ExceptT $ guard c (return $ Left x) (guard d (return $ Right y) (return $ Right z)))
            [(SSBool "a", SSBool "c", 3, 4, 5), (SSBool "b", SSBool "d", 2, 3, 6)] ::
            ExceptT Integer (UnionMBase SBool) [Integer]
        )
        `shouldBe` runExceptT
          ( do
              a <- mrgIf (SSBool "a") (throwError 3) (mrgIf (SSBool "c") (return 4) (return 5))
              b <- mrgIf (SSBool "b") (throwError 2) (mrgIf (SSBool "d") (return 3) (return 6))
              mrgReturn [a, b]
          )
  describe "mrgSequenceA" $
    it "mrgSequenceA should work" $ do
      runExceptT
        ( mrgSequenceA
            [ ExceptT $ guard (SSBool "a") (return $ Left 3) (guard (SSBool "c") (return $ Right 4) (return $ Right 5)),
              ExceptT $ guard (SSBool "b") (return $ Left 2) (guard (SSBool "d") (return $ Right 3) (return $ Right 6))
            ] ::
            ExceptT Integer (UnionMBase SBool) [Integer]
        )
        `shouldBe` runExceptT
          ( do
              a <- mrgIf (SSBool "a") (throwError 3) (mrgIf (SSBool "c") (return 4) (return 5))
              b <- mrgIf (SSBool "b") (throwError 2) (mrgIf (SSBool "d") (return 3) (return 6))
              mrgReturn [a, b]
          )
  describe "mrgMapM" $
    it "mrgMapM should work" $ do
      runExceptT
        ( mrgMapM
            (\(c, d, x, y, z) -> ExceptT $ guard c (return $ Left x) (guard d (return $ Right y) (return $ Right z)))
            [(SSBool "a", SSBool "c", 3, 4, 5), (SSBool "b", SSBool "d", 2, 3, 6)] ::
            ExceptT Integer (UnionMBase SBool) [Integer]
        )
        `shouldBe` runExceptT
          ( do
              a <- mrgIf (SSBool "a") (throwError 3) (mrgIf (SSBool "c") (return 4) (return 5))
              b <- mrgIf (SSBool "b") (throwError 2) (mrgIf (SSBool "d") (return 3) (return 6))
              mrgReturn [a, b]
          )
  describe "mrgSequence" $
    it "mrgSequence should work" $ do
      runExceptT
        ( mrgSequence
            [ ExceptT $ guard (SSBool "a") (return $ Left 3) (guard (SSBool "c") (return $ Right 4) (return $ Right 5)),
              ExceptT $ guard (SSBool "b") (return $ Left 2) (guard (SSBool "d") (return $ Right 3) (return $ Right 6))
            ] ::
            ExceptT Integer (UnionMBase SBool) [Integer]
        )
        `shouldBe` runExceptT
          ( do
              a <- mrgIf (SSBool "a") (throwError 3) (mrgIf (SSBool "c") (return 4) (return 5))
              b <- mrgIf (SSBool "b") (throwError 2) (mrgIf (SSBool "d") (return 3) (return 6))
              mrgReturn [a, b]
          )
  describe "mrgFor" $
    it "mrgFor should work" $ do
      runExceptT
        ( mrgFor
            [(SSBool "a", SSBool "c", 3, 4, 5), (SSBool "b", SSBool "d", 2, 3, 6)]
            (\(c, d, x, y, z) -> ExceptT $ guard c (return $ Left x) (guard d (return $ Right y) (return $ Right z))) ::
            ExceptT Integer (UnionMBase SBool) [Integer]
        )
        `shouldBe` runExceptT
          ( do
              a <- mrgIf (SSBool "a") (throwError 3) (mrgIf (SSBool "c") (return 4) (return 5))
              b <- mrgIf (SSBool "b") (throwError 2) (mrgIf (SSBool "d") (return 3) (return 6))
              mrgReturn [a, b]
          )
  describe "mrgForM" $
    it "mrgForM should work" $ do
      runExceptT
        ( mrgForM
            [(SSBool "a", SSBool "c", 3, 4, 5), (SSBool "b", SSBool "d", 2, 3, 6)]
            (\(c, d, x, y, z) -> ExceptT $ guard c (return $ Left x) (guard d (return $ Right y) (return $ Right z))) ::
            ExceptT Integer (UnionMBase SBool) [Integer]
        )
        `shouldBe` runExceptT
          ( do
              a <- mrgIf (SSBool "a") (throwError 3) (mrgIf (SSBool "c") (return 4) (return 5))
              b <- mrgIf (SSBool "b") (throwError 2) (mrgIf (SSBool "d") (return 3) (return 6))
              mrgReturn [a, b]
          )
