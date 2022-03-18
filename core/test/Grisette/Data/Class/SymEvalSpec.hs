{-# LANGUAGE OverloadedStrings #-}

module Grisette.Data.Class.SymEvalSpec where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import qualified Data.HashMap.Strict as M
import Grisette.Data.Class.SymEval
import Test.Hspec
import Test.Hspec.QuickCheck
import Utils.SBool

concreteSymEvalOkSpec :: (SymEval (M.HashMap Symbol Bool) a, Show a, Eq a) => a -> Expectation
concreteSymEvalOkSpec x = symeval True (M.empty :: M.HashMap Symbol Bool) x `shouldBe` x

spec :: Spec
spec = do
  describe "SymEval for common types" $ do
    describe "SymEval for SBool" $ do
      it "SymEval for SBool with empty model / no fill default" $ do
        let model = M.empty :: M.HashMap Symbol Bool
        symeval False model (CBool True) `shouldBe` CBool True
        symeval False model (SSBool "a") `shouldBe` SSBool "a"
        symeval False model (ISBool 1 "a") `shouldBe` ISBool 1 "a"
        symeval False model (Or (SSBool "a") (SSBool "b"))
          `shouldBe` Or (SSBool "a") (SSBool "b")
        symeval False model (And (SSBool "a") (SSBool "b"))
          `shouldBe` And (SSBool "a") (SSBool "b")
        symeval False model (Equal (SSBool "a") (SSBool "b"))
          `shouldBe` Equal (SSBool "a") (SSBool "b")
        symeval False model (Not (SSBool "a"))
          `shouldBe` Not (SSBool "a")
        symeval False model (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
          `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "c")
      it "SymEval for SBool with empty model / with fill default" $ do
        let model = M.empty :: M.HashMap Symbol Bool
        symeval True model (CBool True) `shouldBe` CBool True
        symeval True model (SSBool "a") `shouldBe` CBool False
        symeval True model (ISBool 1 "a") `shouldBe` CBool False
        symeval True model (Or (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        symeval True model (And (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        symeval True model (Equal (SSBool "a") (SSBool "b")) `shouldBe` CBool True
        symeval True model (Not (SSBool "a")) `shouldBe` CBool True
        symeval True model (ITE (SSBool "a") (SSBool "b") (SSBool "c")) `shouldBe` CBool False
      it "SymEval for SBool with some model" $ do
        let model =
              M.fromList
                [ (SSymbol "a", True),
                  (ISymbol 1 "a", False),
                  (SSymbol "b", False),
                  (SSymbol "c", True)
                ] ::
                M.HashMap Symbol Bool
        symeval True model (CBool True) `shouldBe` CBool True
        symeval True model (SSBool "a") `shouldBe` CBool True
        symeval True model (ISBool 1 "a") `shouldBe` CBool False
        symeval True model (Or (SSBool "a") (SSBool "b")) `shouldBe` CBool True
        symeval True model (And (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        symeval True model (Equal (SSBool "a") (SSBool "b")) `shouldBe` CBool False
        symeval True model (Not (SSBool "a")) `shouldBe` CBool False
        symeval True model (ITE (SSBool "a") (SSBool "b") (SSBool "c")) `shouldBe` CBool False
    describe "SymEval for Bool" $ do
      prop "SymEval for Bool should work" (concreteSymEvalOkSpec @Bool)
    describe "SymEval for Integer" $ do
      prop "SymEval for Integer should work" (concreteSymEvalOkSpec @Integer)
    describe "SymEval for Char" $ do
      prop "SymEval for Char should work" (concreteSymEvalOkSpec @Char)
    describe "SymEval for List" $ do
      prop "SymEval for concrete List should work" (concreteSymEvalOkSpec @[Integer])
      it "SymEval for List should work" $ do
        let model =
              M.fromList
                [ (SSymbol "a", True),
                  (SSymbol "b", False)
                ] ::
                M.HashMap Symbol Bool
        symeval True model ([] :: [SBool]) `shouldBe` []
        symeval False model ([] :: [SBool]) `shouldBe` []
        symeval False model [SSBool "a", SSBool "b", SSBool "c"] `shouldBe` [CBool True, CBool False, SSBool "c"]
        symeval True model [SSBool "a", SSBool "b", SSBool "c"] `shouldBe` [CBool True, CBool False, CBool False]
    describe "SymEval for Maybe" $ do
      prop "SymEval for concrete Maybe should work" (concreteSymEvalOkSpec @(Maybe Integer))
      it "SymEval for Maybe should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (Nothing :: Maybe SBool) `shouldBe` Nothing
        symeval True model (Nothing :: Maybe SBool) `shouldBe` Nothing
        symeval False model (Just (SSBool "a")) `shouldBe` Just (CBool True)
        symeval True model (Just (SSBool "a")) `shouldBe` Just (CBool True)
        symeval False model (Just (SSBool "b")) `shouldBe` Just (SSBool "b")
        symeval True model (Just (SSBool "b")) `shouldBe` Just (CBool False)
    describe "SymEval for Either" $ do
      prop "SymEval for concrete Either should work" (concreteSymEvalOkSpec @(Either Integer Integer))
      it "SymEval for Either should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (Left (SSBool "a") :: Either SBool SBool) `shouldBe` Left (CBool True)
        symeval True model (Left (SSBool "a") :: Either SBool SBool) `shouldBe` Left (CBool True)
        symeval False model (Left (SSBool "b") :: Either SBool SBool) `shouldBe` Left (SSBool "b")
        symeval True model (Left (SSBool "b") :: Either SBool SBool) `shouldBe` Left (CBool False)
        symeval False model (Right (SSBool "a") :: Either SBool SBool) `shouldBe` Right (CBool True)
        symeval True model (Right (SSBool "a") :: Either SBool SBool) `shouldBe` Right (CBool True)
        symeval False model (Right (SSBool "b") :: Either SBool SBool) `shouldBe` Right (SSBool "b")
        symeval True model (Right (SSBool "b") :: Either SBool SBool) `shouldBe` Right (CBool False)
    describe "SymEval for MaybeT" $ do
      prop "SymEval for concrete MaybeT should work" (concreteSymEvalOkSpec @(MaybeT Maybe Integer) . MaybeT)
      it "SymEval for MaybeT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT Nothing
        symeval True model (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT Nothing
        symeval False model (MaybeT $ Just Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT (Just Nothing)
        symeval True model (MaybeT $ Just Nothing :: MaybeT Maybe SBool) `shouldBe` MaybeT (Just Nothing)
        symeval False model (MaybeT $ Just $ Just $ SSBool "a") `shouldBe` MaybeT (Just (Just (CBool True)))
        symeval True model (MaybeT $ Just $ Just $ SSBool "a") `shouldBe` MaybeT (Just (Just (CBool True)))
        symeval False model (MaybeT $ Just $ Just $ SSBool "b") `shouldBe` MaybeT (Just (Just (SSBool "b")))
        symeval True model (MaybeT $ Just $ Just $ SSBool "b") `shouldBe` MaybeT (Just (Just (CBool False)))
    describe "SymEval for ExceptT" $ do
      prop "SymEval for concrete ExceptT should work" (concreteSymEvalOkSpec @(ExceptT Integer Maybe Integer) . ExceptT)
      it "SymEval for MaybeT should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` ExceptT Nothing
        symeval True model (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` ExceptT Nothing

        symeval False model (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ CBool True)
        symeval True model (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ CBool True)
        symeval False model (ExceptT $ Just $ Left $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ SSBool "b")
        symeval True model (ExceptT $ Just $ Left $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Left $ CBool False)

        symeval False model (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ CBool True)
        symeval True model (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ CBool True)
        symeval False model (ExceptT $ Just $ Right $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ SSBool "b")
        symeval True model (ExceptT $ Just $ Right $ SSBool "b" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT (Just $ Right $ CBool False)
    describe "SymEval for ()" $ do
      prop "SymEval for () should work" (concreteSymEvalOkSpec @())
    describe "SymEval for (,)" $ do
      prop "SymEval for concrete (,) should work" (concreteSymEvalOkSpec @(Integer, Integer))
      it "SymEval for (,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (SSBool "a", SSBool "b") `shouldBe` (CBool True, SSBool "b")
        symeval True model (SSBool "a", SSBool "b") `shouldBe` (CBool True, CBool False)
    describe "SymEval for (,,)" $ do
      prop "SymEval for concrete (,,) should work" (concreteSymEvalOkSpec @(Integer, Integer, Integer))
      it "SymEval for (,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (SSBool "a", SSBool "b", SSBool "c") `shouldBe` (CBool True, SSBool "b", SSBool "c")
        symeval True model (SSBool "a", SSBool "b", SSBool "c") `shouldBe` (CBool True, CBool False, CBool False)
    describe "SymEval for (,,,)" $ do
      prop "SymEval for concrete (,,,) should work" (concreteSymEvalOkSpec @(Integer, Integer, Integer, Integer))
      it "SymEval for (,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d")
        symeval True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False)
    describe "SymEval for (,,,,)" $ do
      prop
        "SymEval for concrete (,,,,) should work"
        (concreteSymEvalOkSpec @(Integer, Integer, Integer, Integer, Integer))
      it "SymEval for (,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e")
        symeval True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False)
    describe "SymEval for (,,,,,)" $ do
      prop
        "SymEval for concrete (,,,,,) should work"
        (concreteSymEvalOkSpec @(Integer, Integer, Integer, Integer, Integer, Integer))
      it "SymEval for (,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
        symeval True model (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "SymEval for (,,,,,,)" $ do
      prop
        "SymEval for concrete (,,,,,,) should work"
        (concreteSymEvalOkSpec @(Integer, Integer, Integer, Integer, Integer, Integer, Integer))
      it "SymEval for (,,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval
          False
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g")
        symeval
          True
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "h")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "SymEval for (,,,,,,,)" $ do
      prop
        "SymEval for concrete (,,,,,,,) should work"
        (concreteSymEvalOkSpec @(Integer, Integer, Integer, Integer, Integer, Integer, Integer, Integer))
      it "SymEval for (,,,,,,,) should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval
          False
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g", SSBool "h")
          `shouldBe` (CBool True, SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "g", SSBool "h")
        symeval
          True
          model
          (SSBool "a", SSBool "b", SSBool "c", SSBool "d", SSBool "e", SSBool "f", SSBool "h", SSBool "h")
          `shouldBe` (CBool True, CBool False, CBool False, CBool False, CBool False, CBool False, CBool False, CBool False)
    describe "SymEval for ByteString" $
      it "SymEval for ByteString should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model ("" :: B.ByteString) `shouldBe` ""
        symeval True model ("" :: B.ByteString) `shouldBe` ""
        symeval False model ("a" :: B.ByteString) `shouldBe` "a"
        symeval True model ("a" :: B.ByteString) `shouldBe` "a"
    describe "SymEval for Sum" $ do
      prop
        "SymEval for concrete Sum should work"
        ( \(x :: Either (Maybe Integer) (Maybe Integer)) -> case x of
            Left val -> concreteSymEvalOkSpec @(Sum Maybe Maybe Integer) $ InL val
            Right val -> concreteSymEvalOkSpec @(Sum Maybe Maybe Integer) $ InR val
        )
      it "SymEval for Sum should work" $ do
        let model = M.fromList [(SSymbol "a", True)] :: M.HashMap Symbol Bool
        symeval False model (InL Nothing :: Sum Maybe Maybe SBool) `shouldBe` InL Nothing
        symeval True model (InL Nothing :: Sum Maybe Maybe SBool) `shouldBe` InL Nothing
        symeval False model (InR Nothing :: Sum Maybe Maybe SBool) `shouldBe` InR Nothing
        symeval True model (InR Nothing :: Sum Maybe Maybe SBool) `shouldBe` InR Nothing

        symeval False model (InL (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ CBool True)
        symeval True model (InL (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ CBool True)
        symeval False model (InL (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ SSBool "b")
        symeval True model (InL (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InL (Just $ CBool False)

        symeval False model (InR (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ CBool True)
        symeval True model (InR (Just $ SSBool "a") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ CBool True)
        symeval False model (InR (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ SSBool "b")
        symeval True model (InR (Just $ SSBool "b") :: Sum Maybe Maybe SBool) `shouldBe` InR (Just $ CBool False)
