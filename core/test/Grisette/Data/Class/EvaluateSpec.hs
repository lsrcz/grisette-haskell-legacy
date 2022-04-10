{-# LANGUAGE OverloadedStrings #-}

module Grisette.Data.Class.EvaluateSpec where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import qualified Data.HashMap.Strict as M
import Grisette.Data.Class.Evaluate
import Test.Hspec
import Test.Hspec.QuickCheck
import Utils.SBool

concreteEvaluateOkSpec :: (HasCallStack, Evaluate (M.HashMap Symbol Bool) a, Show a, Eq a) => a -> Expectation
concreteEvaluateOkSpec x = evaluate True (M.empty :: M.HashMap Symbol Bool) x `shouldBe` x

spec :: Spec
spec = do
  describe "Evaluate for common types" $ do
    describe "Evaluate for SBool" $ do
      it "Evaluate for SBool with empty model / no fill default" $ do
        let model = M.empty :: M.HashMap Symbol Bool
        evaluate False model (CBool True) `shouldBe` CBool True
        evaluate False model (SSBool "a") `shouldBe` SSBool "a"
        evaluate False model (ISBool 1 "a") `shouldBe` ISBool 1 "a"
        evaluate False model (Or (SSBool "a") (SSBool "b"))
          `shouldBe` Or (SSBool "a") (SSBool "b")
        evaluate False model (And (SSBool "a") (SSBool "b"))
          `shouldBe` And (SSBool "a") (SSBool "b")
        evaluate False model (Equal (SSBool "a") (SSBool "b"))
          `shouldBe` Equal (SSBool "a") (SSBool "b")
        evaluate False model (Not (SSBool "a"))
          `shouldBe` Not (SSBool "a")
        evaluate False model (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
          `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "c")
      it "Evaluate for SBool with empty model / with fill default" $ do
        let model = M.empty :: M.HashMap Symbol Bool
        evaluate True model (CBool True) `shouldBe` CBool True
        evaluate True model (SSBool "a") `shouldBe` CBool False
        evaluate True model (ISBool 1 "a") `shouldBe` CBool False
        evaluate True model (Or (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (And (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (Equal (SSBool "a") (SSBool "b")) `shouldBe` CBool True
        evaluate True model (Not (SSBool "a")) `shouldBe` CBool True
        evaluate True model (ITE (SSBool "a") (SSBool "b") (SSBool "c")) `shouldBe` CBool False
      it "Evaluate for SBool with some model" $ do
        let model =
              M.fromList
                [ (SSymbol "a", True),
                  (ISymbol 1 "a", False),
                  (SSymbol "b", False),
                  (SSymbol "c", True)
                ] ::
                M.HashMap Symbol Bool
        evaluate True model (CBool True) `shouldBe` CBool True
        evaluate True model (SSBool "a") `shouldBe` CBool True
        evaluate True model (ISBool 1 "a") `shouldBe` CBool False
        evaluate True model (Or (SSBool "a") (SSBool "b")) `shouldBe` CBool True
        evaluate True model (And (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (Equal (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (Not (SSBool "a")) `shouldBe` CBool False
        evaluate True model (ITE (SSBool "a") (SSBool "b") (SSBool "c")) `shouldBe` CBool False
    describe "Evaluate for Bool" $ do
      prop "Evaluate for Bool should work" (concreteEvaluateOkSpec @Bool)
    describe "Evaluate for Integer" $ do
      prop "Evaluate for Integer should work" (concreteEvaluateOkSpec @Integer)
    describe "Evaluate for Char" $ do
      prop "Evaluate for Char should work" (concreteEvaluateOkSpec @Char)
    describe "Evaluate for List" $ do
      prop "Evaluate for concrete List should work" (concreteEvaluateOkSpec @[Integer])
      it "Evaluate for List should work" $ do
        let model =
              M.fromList
                [ (SSymbol "a", True),
                  (SSymbol "b", False)
                ] ::
                M.HashMap Symbol Bool
        evaluate True model ([] :: [SBool]) `shouldBe` []
        evaluate False model ([] :: [SBool]) `shouldBe` []
        evaluate False model [SSBool "a", SSBool "b", SSBool "c"] `shouldBe` [CBool True, CBool False, SSBool "c"]
        evaluate True model [SSBool "a", SSBool "b", SSBool "c"] `shouldBe` [CBool True, CBool False, CBool False]
    describe "Evaluate for Maybe" $ do
      prop "Evaluate for concrete Maybe should work" (concreteEvaluateOkSpec @(Maybe Integer))
      it "Evaluate for Maybe should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (Nothing :: Maybe SBool) `shouldBe` Nothing
        evaluate True model (Nothing :: Maybe SBool) `shouldBe` Nothing
        evaluate False model (Just (SSBool "a")) `shouldBe` Just (CBool True)
        evaluate True model (Just (SSBool "a")) `shouldBe` Just (CBool True)
        evaluate False model (Just (SSBool "b")) `shouldBe` Just (SSBool "b")
        evaluate True model (Just (SSBool "b")) `shouldBe` Just (CBool False)
    describe "Evaluate for Either" $ do
      prop "Evaluate for concrete Either should work" (concreteEvaluateOkSpec @(Either Integer Integer))
      it "Evaluate for Either should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (Left (SSBool "a") :: Either SBool SBool) `shouldBe` Left (CBool True)
        evaluate True model (Left (SSBool "a") :: Either SBool SBool) `shouldBe` Left (CBool True)
        evaluate False model (Left (SSBool "b") :: Either SBool SBool) `shouldBe` Left (SSBool "b")
        evaluate True model (Left (SSBool "b") :: Either SBool SBool) `shouldBe` Left (CBool False)
        evaluate False model (Right (SSBool "a") :: Either SBool SBool) `shouldBe` Right (CBool True)
        evaluate True model (Right (SSBool "a") :: Either SBool SBool) `shouldBe` Right (CBool True)
        evaluate False model (Right (SSBool "b") :: Either SBool SBool) `shouldBe` Right (SSBool "b")
        evaluate True model (Right (SSBool "b") :: Either SBool SBool) `shouldBe` Right (CBool False)
    describe "Evaluate for MaybeT" $ do
      prop "Evaluate for concrete MaybeT should work" (concreteEvaluateOkSpec @(MaybeT Maybe Integer) . MaybeT)
      it "Evaluate for MaybeT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT Nothing
        evaluate True model (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT Nothing
        evaluate False model (MaybeT $ Just Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT (Just Nothing)
        evaluate True model (MaybeT $ Just Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT (Just Nothing)
        evaluate False model (MaybeT $ Just $ Just $ SSBool "a") `shouldBe` MaybeT (Just (Just (CBool True)))
        evaluate True model (MaybeT $ Just $ Just $ SSBool "a") `shouldBe` MaybeT (Just (Just (CBool True)))
        evaluate False model (MaybeT $ Just $ Just $ SSBool "b") `shouldBe` MaybeT (Just (Just (SSBool "b")))
        evaluate True model (MaybeT $ Just $ Just $ SSBool "b") `shouldBe` MaybeT (Just (Just (CBool False)))
    describe "Evaluate for ExceptT" $ do
      prop "Evaluate for concrete ExceptT should work" (concreteEvaluateOkSpec @(ExceptT Integer Maybe Integer) . ExceptT)
      it "Evaluate for MaybeT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` ExceptT Nothing
        evaluate True model (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` ExceptT Nothing

        evaluate False model (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ CBool True)
        evaluate True model (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ CBool True)
        evaluate False model (ExceptT $ Just $ Left $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ SSBool "b")
        evaluate True model (ExceptT $ Just $ Left $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ CBool False)

        evaluate False model (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ CBool True)
        evaluate True model (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ CBool True)
        evaluate False model (ExceptT $ Just $ Right $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ SSBool "b")
        evaluate True model (ExceptT $ Just $ Right $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ CBool False)
    describe "Evaluate for ()" $ do
      prop "Evaluate for () should work" (concreteEvaluateOkSpec @())
    describe "Evaluate for (,)" $ do
      prop "Evaluate for concrete (,) should work" (concreteEvaluateOkSpec @(Integer, Integer))
      it "Evaluate for (,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b") `shouldBe` (CBool True, SSBool "b")
        evaluate True model (SSBool "a", SSBool "b") `shouldBe` (CBool True, CBool False)
    describe "Evaluate for (,,)" $ do
      prop "Evaluate for concrete (,,) should work" (concreteEvaluateOkSpec @(Integer, Integer, Integer))
      it "Evaluate for (,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c") `shouldBe` (CBool True, SSBool "b", SSBool "c")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c") `shouldBe` (CBool True, CBool False, CBool False)
    describe "Evaluate for (,,,)" $ do
      prop "Evaluate for concrete (,,,) should work" (concreteEvaluateOkSpec @(Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,) should work"
        (concreteEvaluateOkSpec @(Integer, Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,,) should work"
        (concreteEvaluateOkSpec @(Integer, Integer, Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,,,) should work"
        (concreteEvaluateOkSpec @(Integer, Integer, Integer, Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate
          False
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g")
        evaluate
          True
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "h")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,,,,) should work"
        (concreteEvaluateOkSpec @(Integer, Integer, Integer, Integer, Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate
          False
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g", SSBool "h")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g", SSBool "h")
        evaluate
          True
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "h", SSBool "h")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "Evaluate for ByteString" $
      it "Evaluate for ByteString should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model ("" :: B.ByteString) `shouldBe` ""
        evaluate True model ("" :: B.ByteString) `shouldBe` ""
        evaluate False model ("a" :: B.ByteString) `shouldBe` "a"
        evaluate True model ("a" :: B.ByteString) `shouldBe` "a"
    describe "Evaluate for Sum" $ do
      prop
        "Evaluate for concrete Sum should work"
        ( \(x :: Either (Maybe Integer) (Maybe Integer)) -> case x of
            Left val -> concreteEvaluateOkSpec @(Sum Maybe Maybe Integer) $ InL val
            Right val -> concreteEvaluateOkSpec @(Sum Maybe Maybe Integer) $ InR val
        )
      it "Evaluate for Sum should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (InL Nothing :: Sum Maybe Maybe SBool) `shouldBe` InL Nothing
        evaluate True model (InL Nothing :: Sum Maybe Maybe SBool) `shouldBe` InL Nothing
        evaluate False model (InR Nothing :: Sum Maybe Maybe SBool) `shouldBe` InR Nothing
        evaluate True model (InR Nothing :: Sum Maybe Maybe SBool) `shouldBe` InR Nothing

        evaluate False model (InL (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ CBool True)
        evaluate True model (InL (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ CBool True)
        evaluate False model (InL (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ SSBool "b")
        evaluate True model (InL (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ CBool False)

        evaluate False model (InR (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ CBool True)
        evaluate True model (InR (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ CBool True)
        evaluate False model (InR (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ SSBool "b")
        evaluate True model (InR (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ CBool False)