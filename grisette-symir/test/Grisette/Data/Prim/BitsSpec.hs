{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Grisette.Data.Prim.BitsSpec where

import qualified Data.BitVector.Sized.Signed as BVS
import qualified Data.BitVector.Sized.Unsigned as BVU
import Grisette.Data.Prim.Bits
import Grisette.Data.Prim.InternedTerm
import Test.Hspec

spec :: Spec
spec = do
  describe "AndBits" $ do
    describe "AndBits construction" $ do
      it "AndBits on both concrete" $ do
        bitand
          (concTerm 3 :: Term (BVU.UnsignedBV 4))
          (concTerm 5)
          `shouldBe` concTerm 1
      it "AndBits with zeroBits" $ do
        bitand
          (concTerm 0 :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "a")
          `shouldBe` concTerm 0
        bitand
          (ssymbTerm "a")
          (concTerm 0 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 0
      it "AndBits with all one bits" $ do
        bitand
          (concTerm 15 :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "a")
          `shouldBe` ssymbTerm "a"
        bitand
          (ssymbTerm "a")
          (concTerm 15 :: Term (BVU.UnsignedBV 4))
          `shouldBe` ssymbTerm "a"
      it "AndBits symbolic" $ do
        bitand
          (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "b")
          `shouldBe` constructBinary
            (AndBits @(BVU.UnsignedBV 4))
            (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
            (ssymbTerm "b" :: Term (BVU.UnsignedBV 4))
    describe "AndBits pattern" $ do
      it "AndBits pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          AndBitsTerm (_ :: Term Bool) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case bitand (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (ssymbTerm "b") of
          AndBitsTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "OrBits" $ do
    describe "OrBits construction" $ do
      it "OrBits on both concrete" $ do
        bitor
          (concTerm 3 :: Term (BVU.UnsignedBV 4))
          (concTerm 5)
          `shouldBe` concTerm 7
      it "OrBits with zeroBits" $ do
        bitor
          (concTerm 0 :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "a")
          `shouldBe` ssymbTerm "a"
        bitor
          (ssymbTerm "a")
          (concTerm 0 :: Term (BVU.UnsignedBV 4))
          `shouldBe` ssymbTerm "a"
      it "OrBits with all one bits" $ do
        bitor
          (concTerm 15 :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "a")
          `shouldBe` concTerm 15
        bitor
          (ssymbTerm "a")
          (concTerm 15 :: Term (BVU.UnsignedBV 4))
          `shouldBe` concTerm 15
      it "OrBits symbolic" $ do
        bitor
          (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "b")
          `shouldBe` constructBinary
            (OrBits @(BVU.UnsignedBV 4))
            (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
            (ssymbTerm "b" :: Term (BVU.UnsignedBV 4))
    describe "OrBits pattern" $ do
      it "OrBits pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          OrBitsTerm (_ :: Term Bool) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case bitor (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (ssymbTerm "b") of
          OrBitsTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "XorBits" $ do
    describe "XorBits construction" $ do
      it "XorBits on both concrete" $ do
        bitxor
          (concTerm 3 :: Term (BVU.UnsignedBV 4))
          (concTerm 5)
          `shouldBe` concTerm 6
      it "XorBits with zeroBits" $ do
        bitxor
          (concTerm 0 :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "a")
          `shouldBe` ssymbTerm "a"
        bitxor
          (ssymbTerm "a")
          (concTerm 0 :: Term (BVU.UnsignedBV 4))
          `shouldBe` ssymbTerm "a"
      it "XorBits with all one bits" $ do
        bitxor
          (concTerm 15 :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "a")
          `shouldBe` bitneg (ssymbTerm "a")
        bitxor
          (ssymbTerm "a")
          (concTerm 15 :: Term (BVU.UnsignedBV 4))
          `shouldBe` bitneg (ssymbTerm "a")
      it "XorBits with single complement" $ do
        bitxor
          (bitneg $ ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "b")
          `shouldBe` bitneg (bitxor (ssymbTerm "a") (ssymbTerm "b"))
        bitxor
          (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (bitneg $ ssymbTerm "b")
          `shouldBe` bitneg (bitxor (ssymbTerm "a") (ssymbTerm "b"))
      it "XorBits with both complement" $ do
        bitxor
          (bitneg $ ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (bitneg $ ssymbTerm "b")
          `shouldBe` bitxor (ssymbTerm "a") (ssymbTerm "b")
      it "XorBits symbolic" $ do
        bitxor
          (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          (ssymbTerm "b")
          `shouldBe` constructBinary
            (XorBits @(BVU.UnsignedBV 4))
            (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
            (ssymbTerm "b" :: Term (BVU.UnsignedBV 4))
    describe "XorBits pattern" $ do
      it "XorBits pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          XorBitsTerm (_ :: Term Bool) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case bitxor (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (ssymbTerm "b") of
          XorBitsTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "ComplementBits" $ do
    describe "ComplementBits construction" $ do
      it "ComplementBits on concrete" $ do
        bitneg (concTerm 5 :: Term (BVU.UnsignedBV 4)) `shouldBe` concTerm 10
      it "ComplementBits on complement" $ do
        bitneg (bitneg (ssymbTerm "a") :: Term (BVU.UnsignedBV 4)) `shouldBe` ssymbTerm "a"
      it "ComplementBits on symbolic" $ do
        bitneg (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
          `shouldBe` constructUnary (ComplementBits @(BVU.UnsignedBV 4)) (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
    describe "ComplementBits pattern" $ do
      it "ComplementBits pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          ComplementBitsTerm _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case bitneg (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) of
          ComplementBitsTerm v1 -> do
            v1 `shouldBe` ssymbTerm "a"
          _ -> return ()
  describe "ShiftBits" $ do
    describe "ShiftBits construction" $ do
      it "ShiftBits on concrete" $ do
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) (-5) `shouldBe` concTerm 0
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) (-4) `shouldBe` concTerm 0
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) (-3) `shouldBe` concTerm 1
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) (-2) `shouldBe` concTerm 3
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) (-1) `shouldBe` concTerm 7
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) 0 `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) 1 `shouldBe` concTerm 14
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) 2 `shouldBe` concTerm 12
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) 3 `shouldBe` concTerm 8
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) 4 `shouldBe` concTerm 0
        bitshift (concTerm 15 :: Term (BVU.UnsignedBV 4)) 5 `shouldBe` concTerm 0

        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) (-5) `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) (-4) `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) (-3) `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) (-2) `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) (-1) `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) 0 `shouldBe` concTerm 15
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) 1 `shouldBe` concTerm 14
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) 2 `shouldBe` concTerm 12
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) 3 `shouldBe` concTerm 8
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) 4 `shouldBe` concTerm 0
        bitshift (concTerm 15 :: Term (BVS.SignedBV 4)) 5 `shouldBe` concTerm 0
      it "ShiftBits 0" $ do
        bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 0 `shouldBe` ssymbTerm "a"
        bitshift (ssymbTerm "a" :: Term (BVS.SignedBV 4)) 0 `shouldBe` ssymbTerm "a"
      it "ShiftBits left bitsize" $ do
        bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 4 `shouldBe` concTerm 0
        bitshift (ssymbTerm "a" :: Term (BVS.SignedBV 4)) 4 `shouldBe` concTerm 0
        bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 5 `shouldBe` concTerm 0
        bitshift (ssymbTerm "a" :: Term (BVS.SignedBV 4)) 5 `shouldBe` concTerm 0
      it "ShiftBits same direction twice" $ do
        bitshift (bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 1) 2
          `shouldBe` bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 3
        bitshift (bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (-1)) (-2)
          `shouldBe` bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (-3)
      it "ShiftBits symbolic" $ do
        bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 2
          `shouldBe` constructUnary
            (ShiftBits 2 :: ShiftBits (BVU.UnsignedBV 4))
            (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
    describe "ShiftBits pattern" $ do
      it "ShiftBits pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          ShiftBitsTerm _ _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 2 of
          ShiftBitsTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` 2
          _ -> return ()
  describe "Rotate" $ do
    describe "Rotate construction" $ do
      it "Rotate on concrete" $ do
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) (-4) `shouldBe` concTerm 3
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) (-3) `shouldBe` concTerm 6
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) (-2) `shouldBe` concTerm 12
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) (-1) `shouldBe` concTerm 9
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) 0 `shouldBe` concTerm 3
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) 1 `shouldBe` concTerm 6
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) 2 `shouldBe` concTerm 12
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) 3 `shouldBe` concTerm 9
        bitrotate (concTerm 3 :: Term (BVU.UnsignedBV 4)) 4 `shouldBe` concTerm 3
      it "Rotate 0" $ do
        bitrotate (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 0 `shouldBe` ssymbTerm "a"
      it "Rotate extra bits" $ do
        bitrotate (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 4 `shouldBe` ssymbTerm "a"
        bitrotate (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 5 `shouldBe`
          bitrotate (ssymbTerm "a") 1
        bitrotate (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) (-1) `shouldBe`
          bitrotate (ssymbTerm "a") 3
      it "Rotate twice" $ do
        bitrotate (bitrotate (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 1) 2
          `shouldBe` bitrotate (ssymbTerm "a") 3
      it "Rotate symbolic" $ do
        bitrotate (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 2
          `shouldBe` constructUnary
            (RotateBits 2 :: RotateBits (BVU.UnsignedBV 4))
            (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
    describe "RotateBits pattern" $ do
      it "RotateBits pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          RotateBitsTerm _ _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case bitshift (ssymbTerm "a" :: Term (BVU.UnsignedBV 4)) 2 of
          RotateBitsTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` 2
          _ -> return ()

