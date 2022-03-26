module Grisette.Data.Prim.BVSpec where

import qualified Data.BitVector.Sized.Signed as BVS
import qualified Data.BitVector.Sized.Unsigned as BVU
import Data.Proxy
import Grisette.Data.Prim.BV
import Grisette.Data.Prim.InternedTerm
import Test.Hspec

spec :: Spec
spec = do
  describe "BVTExtract" $ do
    describe "BVTExtract construction" $ do
      it "BVTExtract on concrete" $ do
        bvtextract
          (Proxy @0)
          (Proxy @1)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 0
        bvtextract
          (Proxy @1)
          (Proxy @1)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 1
        bvtextract
          (Proxy @2)
          (Proxy @1)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 1
        bvtextract
          (Proxy @3)
          (Proxy @1)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 0
        bvtextract
          (Proxy @0)
          (Proxy @2)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 2
        bvtextract
          (Proxy @1)
          (Proxy @2)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 3
        bvtextract
          (Proxy @2)
          (Proxy @2)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 1
        bvtextract
          (Proxy @0)
          (Proxy @3)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 6
        bvtextract
          (Proxy @1)
          (Proxy @3)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 3
        bvtextract
          (Proxy @0)
          (Proxy @4)
          (concTerm 6 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 6
      it "BVTExtract on symbolic" $ do
        bvtextract
          (Proxy @2)
          (Proxy @1)
          (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          `shouldBe` constructUnary (BVTExtract @2 @1 @4 Proxy) (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
    describe "BVTExtract pattern" $ do
      it "extractView should work" $ do
        case extractView (bvtextract (Proxy @1) (Proxy @2) (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))) of
          Just (ExtractMatchResult _ v1 :: ExtractMatchResult BVU.UnsignedBV 2 4) -> do
            True `shouldBe` True
            v1 `shouldBe` ssymbTerm "a"
          _ -> return () :: Expectation
  describe "Extension" $ do
    describe "Extension construction" $ do
      it "Extension on concrete" $ do
        bvtext (Proxy @2) True (concTerm 15 :: Term (BVU.UnsignedBV 4))
          `shouldBe` (concTerm 63 :: Term (BVU.UnsignedBV 6))
        bvtext (Proxy @2) False (concTerm 15 :: Term (BVU.UnsignedBV 4))
          `shouldBe` (concTerm 15 :: Term (BVU.UnsignedBV 6))
        bvtext (Proxy @2) True (concTerm 15 :: Term (BVS.SignedBV 4))
          `shouldBe` (concTerm 63 :: Term (BVS.SignedBV 6))
        bvtext (Proxy @2) False (concTerm 15 :: Term (BVS.SignedBV 4))
          `shouldBe` (concTerm 15 :: Term (BVS.SignedBV 6))
      it "Extension on symbolic" $ do
        bvtext (Proxy @2) True (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          `shouldBe` constructUnary (Sext @2 @4 @6 Proxy) (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
        bvtext (Proxy @2) False (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          `shouldBe` constructUnary (Zext @2 @4 @6 Proxy) (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
    describe "Extension pattern" $ do
      it "extensionView should work" $ do
        case extensionView (bvtext (Proxy @2) True (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))) of
          Just (ExtensionMatchResult _ b v1 :: ExtensionMatchResult BVU.UnsignedBV 4 6) -> do
            b `shouldBe` True
            v1 `shouldBe` ssymbTerm "a"
          _ -> return () :: Expectation
        case extensionView (bvtext (Proxy @2) False (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))) of
          Just (ExtensionMatchResult _ b v1 :: ExtensionMatchResult BVU.UnsignedBV 4 6) -> do
            b `shouldBe` False
            v1 `shouldBe` ssymbTerm "a"
          _ -> return () :: Expectation
  describe "Concat" $ do
    describe "Concat construction" $ do
      it "Concat on concrete" $ do
        bvtconcat (concTerm 3 :: Term (BVU.UnsignedBV 4)) (concTerm 5 :: Term (BVU.UnsignedBV 3))
          `shouldBe` concTerm 29
        bvtconcat (concTerm 3 :: Term (BVS.SignedBV 4)) (concTerm 5 :: Term (BVS.SignedBV 3))
          `shouldBe` concTerm 29
      it "Concat on symbolic" $ do
        bvtconcat (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (ssymbTerm "b" :: Term (BVU.UnsignedBV 3))
          `shouldBe` constructBinary
            (BVTConcat @4 @3)
            (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
            (ssymbTerm "b" :: Term (BVU.UnsignedBV 3))
    describe "Concat pattern" $ do
      it "concatView should work" $ do
        case concatView (bvtconcat (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "b" :: Term (BVU.UnsignedBV 3))) of
          Just (ConcatMatchResult v1 v2 :: ConcatMatchResult BVU.UnsignedBV 3 4 7) -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return () :: Expectation
