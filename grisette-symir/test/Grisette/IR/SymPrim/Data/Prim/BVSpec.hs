{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.IR.SymPrim.Data.Prim.BVSpec where

import Data.Proxy
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.Prim.BV
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Test.Hspec

spec :: Spec
spec = do
  describe "BVTSelect" $ do
    describe "BVTSelect construction" $ do
      it "BVTSelect on concrete" $ do
        bvtselect
          (Proxy @0)
          (Proxy @1)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 0
        bvtselect
          (Proxy @1)
          (Proxy @1)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 1
        bvtselect
          (Proxy @2)
          (Proxy @1)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 1
        bvtselect
          (Proxy @3)
          (Proxy @1)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 0
        bvtselect
          (Proxy @0)
          (Proxy @2)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 2
        bvtselect
          (Proxy @1)
          (Proxy @2)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 3
        bvtselect
          (Proxy @2)
          (Proxy @2)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 1
        bvtselect
          (Proxy @0)
          (Proxy @3)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 6
        bvtselect
          (Proxy @1)
          (Proxy @3)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 3
        bvtselect
          (Proxy @0)
          (Proxy @4)
          (concTerm 6 :: Term (WordN 4))
          `shouldBe` concTerm 6
      it "BVTSelect on symbolic" $ do
        bvtselect
          (Proxy @2)
          (Proxy @1)
          (ssymbTerm "a" :: Term (WordN 4))
          `shouldBe` constructUnary (BVTSelect @WordN @2 @1 @4 Proxy) (ssymbTerm "a" :: Term (WordN 4))
    describe "BVTSelect pattern" $ do
      it "selectView should work" $ do
        case selectView (bvtselect (Proxy @1) (Proxy @2) (ssymbTerm "a" :: Term (WordN 4))) of
          Just (SelectMatchResult _ v1 :: SelectMatchResult WordN 2 4) -> do
            True `shouldBe` True
            v1 `shouldBe` ssymbTerm "a"
          _ -> return () :: Expectation
  describe "Extension" $ do
    describe "Extension construction" $ do
      it "Extension on concrete" $ do
        bvtext (Proxy @6) True (concTerm 15 :: Term (WordN 4))
          `shouldBe` (concTerm 63 :: Term (WordN 6))
        bvtext (Proxy @6) False (concTerm 15 :: Term (WordN 4))
          `shouldBe` (concTerm 15 :: Term (WordN 6))
        bvtext (Proxy @6) True (concTerm 15 :: Term (IntN 4))
          `shouldBe` (concTerm 63 :: Term (IntN 6))
        bvtext (Proxy @6) False (concTerm 15 :: Term (IntN 4))
          `shouldBe` (concTerm 15 :: Term (IntN 6))
      it "Extension on symbolic" $ do
        bvtext (Proxy @6) True (ssymbTerm "a" :: Term (WordN 4))
          `shouldBe` constructUnary (Sext @WordN @4 @6) (ssymbTerm "a" :: Term (WordN 4))
        bvtext (Proxy @6) False (ssymbTerm "a" :: Term (WordN 4))
          `shouldBe` constructUnary (Zext @WordN @4 @6) (ssymbTerm "a" :: Term (WordN 4))
    describe "Extension pattern" $ do
      it "extensionView should work" $ do
        case extensionView (bvtext (Proxy @6) True (ssymbTerm "a" :: Term (WordN 4))) of
          Just (ExtensionMatchResult b v1 :: ExtensionMatchResult WordN 4 6) -> do
            b `shouldBe` True
            v1 `shouldBe` ssymbTerm "a"
          _ -> return () :: Expectation
        case extensionView (bvtext (Proxy @6) False (ssymbTerm "a" :: Term (WordN 4))) of
          Just (ExtensionMatchResult b v1 :: ExtensionMatchResult WordN 4 6) -> do
            b `shouldBe` False
            v1 `shouldBe` ssymbTerm "a"
          _ -> return () :: Expectation
  describe "Concat" $ do
    describe "Concat construction" $ do
      it "Concat on concrete" $ do
        pevalBVConcatTerm (concTerm 3 :: Term (WordN 4)) (concTerm 5 :: Term (WordN 3))
          `shouldBe` concTerm 29
        pevalBVConcatTerm (concTerm 3 :: Term (IntN 4)) (concTerm 5 :: Term (IntN 3))
          `shouldBe` concTerm 29
      it "Concat on symbolic" $ do
        pevalBVConcatTerm (ssymbTerm "a" :: Term (WordN 4)) (ssymbTerm "b" :: Term (WordN 3))
          `shouldBe` bvconcatTerm
            (ssymbTerm "a" :: Term (WordN 4))
            (ssymbTerm "b" :: Term (WordN 3))
