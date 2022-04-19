{-# LANGUAGE ScopedTypeVariables #-}
module Grisette.Data.Prim.IntegerSpec where

import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Test.Hspec
import Test.Hspec.QuickCheck

spec :: Spec
spec = do
  describe "DivI" $ do
    describe "DivI construction" $ do
      prop "DivI on concrete" $ \(i :: Integer, j :: Integer) -> do
        if j /= 0
          then divi (concTerm i) (concTerm j) `shouldBe` concTerm (i `div` j)
          else
            divi (concTerm i) (concTerm j)
              `shouldBe` constructBinary DivI (concTerm i) (concTerm j)
      it "divide by 1" $ do
        divi (ssymbTerm "a" :: Term Integer) (concTerm 1) `shouldBe` ssymbTerm "a"
      it "DivI symbolic" $ do
        divi (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary DivI (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
    describe "DivI pattern" $ do
      it "DivI pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          DivITerm _ _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case divi (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          DivITerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "ModI" $ do
    describe "ModI construction" $ do
      prop "ModI on concrete" $ \(i :: Integer, j :: Integer) -> do
        if j /= 0
          then modi (concTerm i) (concTerm j) `shouldBe` concTerm (i `mod` j)
          else
            modi (concTerm i) (concTerm j)
              `shouldBe` constructBinary ModI (concTerm i) (concTerm j)
      it "mod by 1" $ do
        modi (ssymbTerm "a" :: Term Integer) (concTerm 1) `shouldBe` concTerm 0
      it "mod by -1" $ do
        modi (ssymbTerm "a" :: Term Integer) (concTerm $ -1) `shouldBe` concTerm 0
      it "ModI symbolic" $ do
        modi (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary ModI (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
    describe "ModI pattern" $ do
      it "ModI pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          ModITerm _ _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case divi (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          ModITerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()

