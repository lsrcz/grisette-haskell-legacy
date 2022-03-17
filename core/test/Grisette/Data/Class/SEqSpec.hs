{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveAnyClass #-}
module Grisette.Data.Class.SEqSpec where

import Data.Foldable
import Grisette.Data.Class.Bool
import Test.Hspec
import Utils.SBool
import qualified Data.ByteString as B
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import GHC.Generics
import Test.Hspec.QuickCheck

data A = A1 | A2 SBool | A3 SBool SBool deriving (Generic, Show, Eq, SEq SBool)

concreteSEqOkSpec :: (SEq SBool a, Eq a) => (a, a) -> Expectation
concreteSEqOkSpec (i, j) = do
  i ==~ j `shouldBe` CBool (i == j)
  i /=~ j `shouldBe` CBool (i /= j)

spec :: Spec
spec = do
  describe "SEq for common types" $ do
    it "SEq for SBool" $ do
      let bools :: [Bool] = [True, False]
      traverse_ (\(i, j) -> CBool i ==~ CBool j `shouldBe` CBool (i == j)) [(x, y) | x <- bools, y <- bools]
      CBool True ==~ SSBool "a" `shouldBe` SSBool "a"
      CBool False ==~ SSBool "a" `shouldBe` Not (SSBool "a")
      SSBool "a" ==~ CBool True `shouldBe` SSBool "a"
      SSBool "a" ==~ CBool False `shouldBe` Not (SSBool "a")
      SSBool "a" ==~ SSBool "b" `shouldBe` Equal (SSBool "a") (SSBool "b")
      SSBool "a" ==~ SSBool "a" `shouldBe` CBool True
    prop "SEq for Bool" (concreteSEqOkSpec @Bool)
    prop "SEq for Integer" (concreteSEqOkSpec @Integer)
    prop "SEq for Char" (concreteSEqOkSpec @Char)
    it "SEq for List" $ do
      ([] :: [Bool]) ==~ [] `shouldBe` CBool True
      [SSBool "a"] ==~ [SSBool "b"] `shouldBe` Equal (SSBool "a") (SSBool "b")
      [SSBool "a", SSBool "b"] ==~ [SSBool "c", SSBool "d"] `shouldBe`
        And (SSBool "a" ==~ SSBool "c") (SSBool "b" ==~ SSBool "d")
      [SSBool "a"] ==~ [] `shouldBe` CBool False
      [SSBool "a"] ==~ [SSBool "c", SSBool "d"] `shouldBe` CBool False
    it "SEq for Maybe" $ do
      (Nothing :: Maybe SBool) ==~ Nothing `shouldBe` CBool True
      Just (SSBool "a") ==~ Nothing `shouldBe` CBool False
      Nothing ==~ Just (SSBool "a") `shouldBe` CBool False
      Just (SSBool "a") ==~ Just (SSBool "b") `shouldBe` Equal (SSBool "a") (SSBool "b")
    it "SEq for Either" $ do
      (Left (SSBool "a") :: Either SBool SBool) ==~ Left (SSBool "b") `shouldBe`
        Equal (SSBool "a") (SSBool "b")
      (Right (SSBool "a") :: Either SBool SBool) ==~ Left (SSBool "b") `shouldBe` CBool False
      (Left (SSBool "a") :: Either SBool SBool) ==~ Right (SSBool "b") `shouldBe` CBool False
      (Right (SSBool "a") :: Either SBool SBool) ==~ Right (SSBool "b") `shouldBe`
        Equal (SSBool "a") (SSBool "b")
    it "SEq for MaybeT" $ do
      (MaybeT Nothing :: MaybeT Maybe SBool) ==~ MaybeT Nothing `shouldBe` CBool True
      (MaybeT Nothing :: MaybeT Maybe SBool) ==~ MaybeT (Just Nothing) `shouldBe` CBool False
      (MaybeT Nothing :: MaybeT Maybe SBool) ==~ MaybeT (Just (Just (SSBool "a"))) `shouldBe` CBool False
      MaybeT (Just Nothing) ==~ (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` CBool False
      MaybeT (Just (Just (SSBool "a"))) ==~ (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` CBool False
      MaybeT (Just Nothing) ==~ (MaybeT (Just Nothing) :: MaybeT Maybe SBool) `shouldBe` CBool True
      MaybeT (Just (Just (SSBool "a"))) ==~ (MaybeT (Just Nothing) :: MaybeT Maybe SBool) `shouldBe` CBool False
      MaybeT (Just Nothing) ==~ (MaybeT (Just (Just (SSBool "b"))) :: MaybeT Maybe SBool) `shouldBe` CBool False
      MaybeT (Just (Just (SSBool "a"))) ==~ (MaybeT (Just (Just (SSBool "b"))) :: MaybeT Maybe SBool)
        `shouldBe` Equal (SSBool "a") (SSBool "b")
    it "SEq for ExceptT" $ do
      (ExceptT Nothing :: ExceptT SBool Maybe SBool) ==~ ExceptT Nothing `shouldBe` CBool True
      (ExceptT Nothing :: ExceptT SBool Maybe SBool) ==~ ExceptT (Just (Left (SSBool "a"))) `shouldBe` CBool False
      (ExceptT Nothing :: ExceptT SBool Maybe SBool) ==~ ExceptT (Just (Right (SSBool "a"))) `shouldBe` CBool False
      ExceptT (Just (Left (SSBool "a"))) ==~ (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` CBool False
      ExceptT (Just (Right (SSBool "a"))) ==~ (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` CBool False
      ExceptT (Just (Left (SSBool "a"))) ==~ (ExceptT (Just (Left (SSBool "b"))) :: ExceptT SBool Maybe SBool)
        `shouldBe` Equal (SSBool "a") (SSBool "b")
      ExceptT (Just (Right (SSBool "a"))) ==~ (ExceptT (Just (Left (SSBool "b"))) :: ExceptT SBool Maybe SBool)
        `shouldBe` CBool False
      ExceptT (Just (Left (SSBool "a"))) ==~ (ExceptT (Just (Right (SSBool "b"))) :: ExceptT SBool Maybe SBool)
        `shouldBe` CBool False
      ExceptT (Just (Right (SSBool "a"))) ==~ (ExceptT (Just (Right (SSBool "b"))) :: ExceptT SBool Maybe SBool)
        `shouldBe` Equal (SSBool "a") (SSBool "b")
    it "SEq for (,)" $ do
      (SSBool "a", SSBool "b") ==~ (SSBool "c", SSBool "d") `shouldBe`
        And (Equal (SSBool "a") (SSBool "c")) (Equal (SSBool "b") (SSBool "d"))
    it "SEq for ByteString" $ do
      let bytestrings :: [B.ByteString] = ["", "a", "ab"]
      traverse_ (\(i, j) -> i ==~ j `shouldBe` CBool (i == j)) [(x, y) | x <- bytestrings, y <- bytestrings]
  describe "deriving SEq for ADT" $ do
    it "derived SEq for simple ADT" $ do
      A1 ==~ A1 `shouldBe` CBool True
      A1 ==~ A2 (SSBool "a") `shouldBe` CBool False
      A1 ==~ A3 (SSBool "a") (SSBool "b") `shouldBe` CBool False
      A2 (SSBool "a") ==~ A1 `shouldBe` CBool False
      A2 (SSBool "a") ==~ A2 (SSBool "b") `shouldBe` Equal (SSBool "a") (SSBool "b")
      A2 (SSBool "a") ==~ A3 (SSBool "b") (SSBool "c") `shouldBe` CBool False
      A3 (SSBool "a") (SSBool "b") ==~ A1 `shouldBe` CBool False
      A3 (SSBool "a") (SSBool "b") ==~ A2 (SSBool "c") `shouldBe` CBool False
      A3 (SSBool "a") (SSBool "b") ==~ A3 (SSBool "c") (SSBool "d") `shouldBe`
        And (Equal (SSBool "a") (SSBool "c")) (Equal (SSBool "b") (SSBool "d"))

    