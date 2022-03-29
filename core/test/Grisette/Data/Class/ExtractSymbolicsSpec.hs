{-# LANGUAGE DeriveAnyClass #-}
module Grisette.Data.Class.ExtractSymbolicsSpec where
import Test.Hspec
import qualified Data.HashSet as S
import Utils.SBool
import Grisette.Data.Class.ExtractSymbolics
import Control.Monad.Trans.Maybe
import Control.Monad.Except
import GHC.Generics
import Test.Hspec.QuickCheck

data A = A1 | A2 SBool | A3 SBool SBool deriving (Generic, Show, Eq, ExtractSymbolics (S.HashSet Symbol))

concreteExtractSymbolicsOkSpec :: (HasCallStack, ExtractSymbolics (S.HashSet Symbol) a) => (a, a) -> Expectation
concreteExtractSymbolicsOkSpec x = extractSymbolics x `shouldBe` (S.empty :: S.HashSet Symbol)

spec :: Spec
spec = do
  describe "ExtractSymbolics for common types" $ do
    it "ExtractSymbolics for SBool" $ do
      extractSymbolics (CBool True) `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (SSBool "a") `shouldBe` S.singleton (SSymbol "a")
      extractSymbolics (ISBool 1 "a") `shouldBe` S.singleton (ISymbol 1 "a")
      extractSymbolics (And (SSBool "a") (ISBool 1 "b")) `shouldBe`
        S.fromList [SSymbol "a", ISymbol 1 "b"]
      extractSymbolics (Or (SSBool "a") (ISBool 1 "b")) `shouldBe`
        S.fromList [SSymbol "a", ISymbol 1 "b"]
      extractSymbolics (Equal (SSBool "a") (ISBool 1 "b")) `shouldBe`
        S.fromList [SSymbol "a", ISymbol 1 "b"]
      extractSymbolics (ITE (SSBool "a") (ISBool 1 "b") (SSBool "c")) `shouldBe`
        S.fromList [SSymbol "a", ISymbol 1 "b", SSymbol "c"]
      extractSymbolics (Not $ ISBool 1 "a") `shouldBe` S.singleton (ISymbol 1 "a")
    prop "ExtractSymbolics for Bool" (concreteExtractSymbolicsOkSpec @Bool)
    prop "ExtractSymbolics for Integer" (concreteExtractSymbolicsOkSpec @Integer)
    prop "ExtractSymbolics for Char" (concreteExtractSymbolicsOkSpec @Char)
    it "ExtractSymbolics for List" $ do
      extractSymbolics ([] :: [SBool]) `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics [SSBool "a"] `shouldBe` S.singleton (SSymbol "a")
      extractSymbolics [SSBool "a", SSBool "b"] `shouldBe` S.fromList [SSymbol "a", SSymbol "b"]
    it "ExtractSymbolics for Maybe" $ do
      extractSymbolics (Nothing :: Maybe SBool) `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (Just (SSBool "a")) `shouldBe` S.singleton (SSymbol "a")
    it "ExtractSymbolics for Either" $ do
      extractSymbolics (Left (SSBool "a") :: Either SBool SBool) `shouldBe` S.singleton (SSymbol "a")
      extractSymbolics (Right (SSBool "a") :: Either SBool SBool) `shouldBe` S.singleton (SSymbol "a")
    it "ExtractSymbolics for MaybeT" $ do
      extractSymbolics (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (MaybeT (Just Nothing) :: MaybeT Maybe SBool) `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (MaybeT (Just (Just (SSBool "a")))) `shouldBe` S.singleton (SSymbol "a")
    it "ExtractSymbolics for ExceptT" $ do
      extractSymbolics (ExceptT Nothing :: ExceptT SBool Maybe SBool) `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (ExceptT (Just (Left (SSBool "a"))) :: ExceptT SBool Maybe SBool) `shouldBe`
        S.singleton (SSymbol "a")
      extractSymbolics (ExceptT (Just (Right (SSBool "a"))) :: ExceptT SBool Maybe SBool) `shouldBe`
        S.singleton (SSymbol "a")
    prop "ExtractSymbolics for ()" (concreteExtractSymbolicsOkSpec @())
    it "ExtractSymbolics for (,)" $ do
      extractSymbolics (SSBool "a", SSBool "b") `shouldBe` S.fromList [SSymbol "a", SSymbol "b"]
    it "ExtractSymbolics for ByteString" $ do
      extractSymbolics "" `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics "a" `shouldBe` (S.empty :: S.HashSet Symbol)
  describe "deriving ExtractSymbolics for ADT" $ do
    it "derived ExtractSymbolics for simple ADT" $ do
      extractSymbolics A1 `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (A2 (SSBool "a")) `shouldBe` S.singleton (SSymbol "a")
      extractSymbolics (A3 (SSBool "a") (SSBool "b")) `shouldBe` S.fromList [SSymbol "a", SSymbol "b"]
    