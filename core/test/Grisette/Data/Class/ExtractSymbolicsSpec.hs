{-# LANGUAGE DeriveAnyClass #-}
module Grisette.Data.Class.ExtractSymbolicsSpec where
import Test.Hspec
import qualified Data.HashSet as S
import Utils.SBool
import Grisette.Data.Class.ExtractSymbolics
import Data.Foldable
import Control.Monad.Trans.Maybe
import Control.Monad.Except
import GHC.Generics

data A = A1 | A2 SBool | A3 SBool SBool deriving (Generic, Show, Eq, ExtractSymbolics (S.HashSet Symbol))

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
    it "ExtractSymbolics for Bool" $ do
      traverse_ (\x -> extractSymbolics x `shouldBe` (S.empty :: S.HashSet Symbol)) [True, False]
    it "ExtractSymbolics for Integer" $ do
      traverse_ (\(x :: Integer) -> extractSymbolics x `shouldBe` (S.empty :: S.HashSet Symbol))
        [-42, -1, 0, 1, 42]
    it "ExtractSymbolics for Char" $ do
      traverse_ (\(x :: Char) -> extractSymbolics x `shouldBe` (S.empty :: S.HashSet Symbol)) $
        toEnum <$> [0, 1, 42, 97, 255]
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
    it "ExtractSymbolics for (,)" $ do
      extractSymbolics (SSBool "a", SSBool "b") `shouldBe` S.fromList [SSymbol "a", SSymbol "b"]
    it "ExtractSymbolics for ByteString" $ do
      extractSymbolics "" `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics "a" `shouldBe` (S.empty :: S.HashSet Symbol)
    it "derived ExtractSymbolics for ADT" $ do
      extractSymbolics A1 `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics (A2 (SSBool "a")) `shouldBe` S.singleton (SSymbol "a")
      extractSymbolics (A3 (SSBool "a") (SSBool "b")) `shouldBe` S.fromList [SSymbol "a", SSymbol "b"]
    