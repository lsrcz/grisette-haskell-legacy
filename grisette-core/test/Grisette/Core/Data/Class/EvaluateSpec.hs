{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Core.Data.Class.EvaluateSpec where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import qualified Data.ByteString as B
import Data.Functor.Sum
import qualified Data.HashMap.Strict as M
import Data.Int
import Data.Word
import Grisette.Core.Data.Class.Evaluate
import Grisette.TestUtils.Evaluate
import Grisette.TestUtils.SBool
import Test.Hspec
import Test.Hspec.QuickCheck

spec :: Spec
spec = do
  describe "Evaluate for common types" $ do
    describe "Evaluate for SBool" $ do
      it "Evaluate for SBool with empty model / no fill default" $ do
        let model = M.empty :: M.HashMap Symbol Bool
        evaluate False model (CBool True) `shouldBe` CBool True
        evaluate False model (SSBool "a") `shouldBe` SSBool "a"
        evaluate False model (ISBool "a" 1) `shouldBe` ISBool "a" 1
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
        evaluate True model (ISBool "a" 1) `shouldBe` CBool False
        evaluate True model (Or (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (And (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (Equal (SSBool "a") (SSBool "b")) `shouldBe` CBool True
        evaluate True model (Not (SSBool "a")) `shouldBe` CBool True
        evaluate True model (ITE (SSBool "a") (SSBool "b") (SSBool "c")) `shouldBe` CBool False
      it "Evaluate for SBool with some model" $ do
        let model =
              M.fromList
                [ (SSymbol "a", True),
                  (ISymbol "a" 1, False),
                  (SSymbol "b", False),
                  (SSymbol "c", True)
                ] ::
                M.HashMap Symbol Bool
        evaluate True model (CBool True) `shouldBe` CBool True
        evaluate True model (SSBool "a") `shouldBe` CBool True
        evaluate True model (ISBool "a" 1) `shouldBe` CBool False
        evaluate True model (Or (SSBool "a") (SSBool "b")) `shouldBe` CBool True
        evaluate True model (And (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (Equal (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        evaluate True model (Not (SSBool "a")) `shouldBe` CBool False
        evaluate True model (ITE (SSBool "a") (SSBool "b") (SSBool "c")) `shouldBe` CBool False
    describe "Evaluate for Bool" $ do
      prop "Evaluate for Bool should work" (concreteEvaluateOkProp @Bool)
    describe "Evaluate for Integer" $ do
      prop "Evaluate for Integer should work" (concreteEvaluateOkProp @Integer)
    describe "Evaluate for Char" $ do
      prop "Evaluate for Char should work" (concreteEvaluateOkProp @Char)

    describe "Evaluate for Int" $ do
      prop "Evaluate for Int should work" (concreteEvaluateOkProp @Int)
    describe "Evaluate for Int8" $ do
      prop "Evaluate for Int8 should work" (concreteEvaluateOkProp @Int8)
    describe "Evaluate for Int16" $ do
      prop "Evaluate for Int16 should work" (concreteEvaluateOkProp @Int16)
    describe "Evaluate for Int32" $ do
      prop "Evaluate for Int32 should work" (concreteEvaluateOkProp @Int32)
    describe "Evaluate for Int64" $ do
      prop "Evaluate for Int64 should work" (concreteEvaluateOkProp @Int64)
    describe "Evaluate for Word" $ do
      prop "Evaluate for Word should work" (concreteEvaluateOkProp @Word)
    describe "Evaluate for Word8" $ do
      prop "Evaluate for Word8 should work" (concreteEvaluateOkProp @Word8)
    describe "Evaluate for Word16" $ do
      prop "Evaluate for Word16 should work" (concreteEvaluateOkProp @Word16)
    describe "Evaluate for Word32" $ do
      prop "Evaluate for Word32 should work" (concreteEvaluateOkProp @Word32)
    describe "Evaluate for Word64" $ do
      prop "Evaluate for Word64 should work" (concreteEvaluateOkProp @Word64)

    describe "Evaluate for List" $ do
      prop "Evaluate for concrete List should work" (concreteEvaluateOkProp @[Integer])
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
      prop "Evaluate for concrete Maybe should work" (concreteEvaluateOkProp @(Maybe Integer))
      it "Evaluate for Maybe should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (Nothing :: Maybe SBool) `shouldBe` Nothing
        evaluate True model (Nothing :: Maybe SBool) `shouldBe` Nothing
        evaluate False model (Just (SSBool "a")) `shouldBe` Just (CBool True)
        evaluate True model (Just (SSBool "a")) `shouldBe` Just (CBool True)
        evaluate False model (Just (SSBool "b")) `shouldBe` Just (SSBool "b")
        evaluate True model (Just (SSBool "b")) `shouldBe` Just (CBool False)
    describe "Evaluate for Either" $ do
      prop "Evaluate for concrete Either should work" (concreteEvaluateOkProp @(Either Integer Integer))
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
      prop "Evaluate for concrete MaybeT should work" (concreteEvaluateOkProp @(MaybeT Maybe Integer) . MaybeT)
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
      prop "Evaluate for concrete ExceptT should work" (concreteEvaluateOkProp @(ExceptT Integer Maybe Integer) . ExceptT)
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
      prop "Evaluate for () should work" (concreteEvaluateOkProp @())
    describe "Evaluate for (,)" $ do
      prop "Evaluate for concrete (,) should work" (concreteEvaluateOkProp @(Integer, Integer))
      it "Evaluate for (,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b") `shouldBe` (CBool True, SSBool "b")
        evaluate True model (SSBool "a", SSBool "b") `shouldBe` (CBool True, CBool False)
    describe "Evaluate for (,,)" $ do
      prop "Evaluate for concrete (,,) should work" (concreteEvaluateOkProp @(Integer, Integer, Integer))
      it "Evaluate for (,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c") `shouldBe` (CBool True, SSBool "b", SSBool "c")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c") `shouldBe` (CBool True, CBool False, CBool False)
    describe "Evaluate for (,,,)" $ do
      prop "Evaluate for concrete (,,,) should work" (concreteEvaluateOkProp @(Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,) should work"
        (concreteEvaluateOkProp @(Integer, Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,,) should work"
        (concreteEvaluateOkProp @(Integer, Integer, Integer, Integer, Integer, Integer))
      it "Evaluate for (,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
        evaluate True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "Evaluate for (,,,,,,)" $ do
      prop
        "Evaluate for concrete (,,,,,,) should work"
        (concreteEvaluateOkProp @(Integer, Integer, Integer, Integer, Integer, Integer, Integer))
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
        (concreteEvaluateOkProp @(Integer, Integer, Integer, Integer, Integer, Integer, Integer, Integer))
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
            Left val -> concreteEvaluateOkProp @(Sum Maybe Maybe Integer) $ InL val
            Right val -> concreteEvaluateOkProp @(Sum Maybe Maybe Integer) $ InR val
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
    describe "Evaluate for WriterT" $ do
      prop
        "Evaluate for concrete Lazy WriterT should work"
        (\(x :: Either Integer (Integer, Integer)) -> concreteEvaluateOkProp (WriterLazy.WriterT x))
      it "Evaluate for general Lazy WriteT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (WriterLazy.WriterT $ Left $ SSBool "a" :: WriterLazy.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterLazy.WriterT (Left $ CBool True)
        evaluate True model (WriterLazy.WriterT $ Left $ SSBool "a" :: WriterLazy.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterLazy.WriterT (Left $ CBool True)
        evaluate False model (WriterLazy.WriterT $ Left $ SSBool "b" :: WriterLazy.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterLazy.WriterT (Left $ SSBool "b")
        evaluate True model (WriterLazy.WriterT $ Left $ SSBool "b" :: WriterLazy.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterLazy.WriterT (Left $ CBool False)

        evaluate False model (WriterLazy.WriterT $ Right (SSBool "a", SSBool "b") :: WriterLazy.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterLazy.WriterT (Right (CBool True, SSBool "b"))
        evaluate True model (WriterLazy.WriterT $ Right (SSBool "a", SSBool "b") :: WriterLazy.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterLazy.WriterT (Right (CBool True, CBool False))
      prop
        "Evaluate for concrete Strict WriterT should work"
        (\(x :: Either Integer (Integer, Integer)) -> concreteEvaluateOkProp (WriterStrict.WriterT x))
      it "Evaluate for general Strict WriteT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (WriterStrict.WriterT $ Left $ SSBool "a" :: WriterStrict.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterStrict.WriterT (Left $ CBool True)
        evaluate True model (WriterStrict.WriterT $ Left $ SSBool "a" :: WriterStrict.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterStrict.WriterT (Left $ CBool True)
        evaluate False model (WriterStrict.WriterT $ Left $ SSBool "b" :: WriterStrict.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterStrict.WriterT (Left $ SSBool "b")
        evaluate True model (WriterStrict.WriterT $ Left $ SSBool "b" :: WriterStrict.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterStrict.WriterT (Left $ CBool False)

        evaluate False model (WriterStrict.WriterT $ Right (SSBool "a", SSBool "b") :: WriterStrict.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterStrict.WriterT (Right (CBool True, SSBool "b"))
        evaluate True model (WriterStrict.WriterT $ Right (SSBool "a", SSBool "b") :: WriterStrict.WriterT SBool (Either SBool) SBool)
          `shouldBe` WriterStrict.WriterT (Right (CBool True, CBool False))
    describe "Evaluate for Identity" $ do
      prop "Evaluate for concrete Identity should work" $
        (\(x :: Integer) -> concreteEvaluateOkProp $ Identity x)
      it "Evaluate for general Identity should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (Identity $ SSBool "a") `shouldBe` Identity (CBool True)
        evaluate True model (Identity $ SSBool "a") `shouldBe` Identity (CBool True)
        evaluate False model (Identity $ SSBool "b") `shouldBe` Identity (SSBool "b")
        evaluate True model (Identity $ SSBool "b") `shouldBe` Identity (CBool False)
    describe "Evaluate for IdentityT" $ do
      prop
        "Evaluate for concrete IdentityT should work"
        (\(x :: Either Integer Integer) -> concreteEvaluateOkProp $ IdentityT x)
      it "Evaluate for general IdentityT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        evaluate False model (IdentityT $ Left $ SSBool "a" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Left $ CBool True)
        evaluate True model (IdentityT $ Left $ SSBool "a" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Left $ CBool True)
        evaluate False model (IdentityT $ Left $ SSBool "b" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Left $ SSBool "b")
        evaluate True model (IdentityT $ Left $ SSBool "b" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Left $ CBool False)
        evaluate False model (IdentityT $ Right $ SSBool "a" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Right $ CBool True)
        evaluate True model (IdentityT $ Right $ SSBool "a" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Right $ CBool True)
        evaluate False model (IdentityT $ Right $ SSBool "b" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Right $ SSBool "b")
        evaluate True model (IdentityT $ Right $ SSBool "b" :: IdentityT (Either SBool) SBool)
          `shouldBe` IdentityT (Right $ CBool False)
