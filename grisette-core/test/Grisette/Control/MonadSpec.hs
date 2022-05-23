{-# LANGUAGE ScopedTypeVariables #-}
module Grisette.Control.MonadSpec where


import Grisette.Control.Monad
import Grisette.Control.Monad.Union
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Test.Hspec
import Utils.SBool
import Control.Monad.Trans.Maybe

spec :: Spec
spec = do
  describe "mrgFoldM" $ do
    it "mrgFoldM should work" $ do
      ( mrgFoldM
          (\acc (c, v) -> guard c (single $ acc + v) (single $ acc * v))
          10
          [(SSBool "a", 2), (SSBool "b", 3)] ::
          UnionMBase SBool Integer
        )
        `shouldBe` mrgIf
          (SSBool "a")
          (mrgIf (SSBool "b") (mrgReturn 15) (mrgReturn 36))
          (mrgIf (SSBool "b") (mrgReturn 23) (mrgReturn 60))
  describe "mrgMzero" $ do
    it "mrgMzero should work" $ do
      (mrgMzero :: MaybeT (UnionMBase SBool) Integer) `shouldBe` MaybeT (mrgReturn Nothing)
  describe "mrgMplus" $ do
    it "mrgMplus should work" $ do
      (mrgMzero `mrgMplus` mrgMzero :: MaybeT (UnionMBase SBool) Integer) `shouldBe` MaybeT (mrgReturn Nothing)
      (mrgReturn 1 `mrgMplus` mrgMzero :: MaybeT (UnionMBase SBool) Integer)
        `shouldBe` mrgReturn 1
      (mrgMzero `mrgMplus` mrgReturn 1 :: MaybeT (UnionMBase SBool) Integer)
        `shouldBe` mrgReturn 1
      (mrgReturn 2 `mrgMplus` mrgReturn 1 :: MaybeT (UnionMBase SBool) Integer)
        `shouldBe` mrgReturn 2
  describe "mrgFmap" $ do
    it "mrgFmap should work" $ do
      mrgFmap (\x -> x * x) (mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn $ 1) :: UnionMBase SBool Integer)
        `shouldBe` mrgReturn 1
  describe ">>~" $ do
    it ">>~ should work" $ do
      (guard (SSBool "a") (single $ -1) (single 1) :: UnionMBase SBool Integer)
        >>~ guard (SSBool "a") (single $ -1) (single 1)
        `shouldBe` (mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn 1) :: UnionMBase SBool Integer)
