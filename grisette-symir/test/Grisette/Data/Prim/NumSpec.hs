{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Grisette.Data.Prim.NumSpec where

import qualified Data.BitVector.Sized.Signed as BVS
import qualified Data.BitVector.Sized.Unsigned as BVU
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Num
import Test.Hspec

spec :: Spec
spec = do
  describe "Add" $ do
    describe "Add construction" $ do
      it "Add on concrete" $ do
        addNum (concTerm 1 :: Term Integer) (concTerm 2) `shouldBe` concTerm 3
        addNum (concTerm 1 :: Term (BVU.UnsignedBV 3)) (concTerm 2) `shouldBe` concTerm 3
        addNum (concTerm 1 :: Term (BVS.SignedBV 3)) (concTerm 2) `shouldBe` concTerm 3
      it "Add on left 0" $ do
        addNum (concTerm 0 :: Term Integer) (ssymbTerm "a") `shouldBe` ssymbTerm "a"
      it "Add on right 0" $ do
        addNum (ssymbTerm "a") (concTerm 0 :: Term Integer) `shouldBe` ssymbTerm "a"
      it "Add on left concrete" $ do
        addNum (concTerm 1 :: Term Integer) (ssymbTerm "a")
          `shouldBe` constructBinary (AddNum @Integer) (concTerm 1 :: Term Integer) (ssymbTerm "a" :: Term Integer)
      it "Add on right concrete" $ do
        addNum (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` constructBinary (AddNum @Integer) (concTerm 1 :: Term Integer) (ssymbTerm "a" :: Term Integer)
      it "Add on no concrete" $ do
        addNum (ssymbTerm "a") (ssymbTerm "b" :: Term Integer)
          `shouldBe` constructBinary (AddNum @Integer) (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
      it "Add when left concrete right add concrete value" $ do
        addNum (concTerm 1 :: Term Integer) (addNum (concTerm 2 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` addNum (concTerm 3 :: Term Integer) (ssymbTerm "a")
      it "Add when right concrete left add concrete value" $ do
        addNum (addNum (concTerm 2 :: Term Integer) (ssymbTerm "a")) (concTerm 1 :: Term Integer)
          `shouldBe` addNum (concTerm 3 :: Term Integer) (ssymbTerm "a")
      it "Add when left add concrete" $ do
        addNum (addNum (concTerm 2 :: Term Integer) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` addNum (concTerm 2 :: Term Integer) (addNum (ssymbTerm "a") (ssymbTerm "b"))
      it "Add when right add concrete" $ do
        addNum (ssymbTerm "b") (addNum (concTerm 2 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` addNum (concTerm 2 :: Term Integer) (addNum (ssymbTerm "b") (ssymbTerm "a"))
      it "Add when both uminus" $ do
        addNum (uminusNum $ ssymbTerm "a" :: Term Integer) (uminusNum $ ssymbTerm "b")
          `shouldBe` uminusNum (addNum (ssymbTerm "a") (ssymbTerm "b"))
      it "Add when both times the same concrete" $ do
        addNum
          (timesNum (concTerm 3) (ssymbTerm "a") :: Term Integer)
          (timesNum (concTerm 3) (ssymbTerm "b"))
          `shouldBe` timesNum (concTerm 3) (addNum (ssymbTerm "a") (ssymbTerm "b"))
      it "Add when both times the same symbolic" $ do
        addNum
          (timesNum (concTerm 3) (ssymbTerm "a") :: Term Integer)
          (timesNum (concTerm 3) (ssymbTerm "a"))
          `shouldBe` timesNum (concTerm 6) (ssymbTerm "a")
        addNum
          (timesNum (concTerm 3) (ssymbTerm "a") :: Term Integer)
          (timesNum (concTerm 4) (ssymbTerm "a"))
          `shouldBe` timesNum (concTerm 7) (ssymbTerm "a")
      it "Add unfold 1" $ do
        addNum
          (concTerm 3)
          (iteterm (ssymbTerm "a") (concTerm 1 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` iteterm (ssymbTerm "a") (concTerm 4) (addNum (concTerm 3) (ssymbTerm "a"))
        addNum
          (iteterm (ssymbTerm "a") (concTerm 1 :: Term Integer) (ssymbTerm "a"))
          (concTerm 3)
          `shouldBe` iteterm (ssymbTerm "a") (concTerm 4) (addNum (ssymbTerm "a") (concTerm 3))
    describe "Add pattern" $ do
      it "Add pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          AddNumTerm (_ :: Term Integer) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case addNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          AddNumTerm (_ :: Term (BVU.UnsignedBV 3)) _ -> expectationFailure "EqvTerm pattern should check type"
          AddNumTerm (v1 :: Term Integer) v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "minus" $ do
    it "minus num should be delegated to add and uminus" $ do
      minusNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
        `shouldBe` addNum (ssymbTerm "a") (uminusNum $ ssymbTerm "b")
  describe "UMinus" $ do
    describe "UMinus construction" $ do
      it "UMinus on concrete" $ do
        uminusNum (concTerm 1 :: Term Integer) `shouldBe` concTerm (-1)
        uminusNum (concTerm 1 :: Term (BVU.UnsignedBV 3)) `shouldBe` concTerm (-1)
      it "UMinus on UMinus" $ do
        uminusNum (uminusNum (ssymbTerm "a" :: Term Integer)) `shouldBe` ssymbTerm "a"
      it "UMinus on Add concrete" $ do
        uminusNum (addNum (concTerm 1) (ssymbTerm "a" :: Term Integer))
          `shouldBe` addNum (concTerm $ -1) (uminusNum $ ssymbTerm "a")
      it "UMinus on Add uminus" $ do
        uminusNum (addNum (uminusNum $ ssymbTerm "a") (ssymbTerm "b" :: Term Integer))
          `shouldBe` addNum (ssymbTerm "a") (uminusNum $ ssymbTerm "b")
        uminusNum (addNum (ssymbTerm "a") (uminusNum $ ssymbTerm "b" :: Term Integer))
          `shouldBe` addNum (uminusNum $ ssymbTerm "a") (ssymbTerm "b")
      it "UMinus on Times concrete" $ do
        uminusNum (timesNum (concTerm 3) (ssymbTerm "a" :: Term Integer))
          `shouldBe` timesNum (concTerm $ -3) (ssymbTerm "a")
      it "UMinus symbolic" $ do
        uminusNum (ssymbTerm "a" :: Term Integer)
          `shouldBe` constructUnary UMinusNum (ssymbTerm "a")
    describe "UMinus pattern" $ do
      it "UMinus pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          UMinusNumTerm (_ :: Term Integer) -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case uminusNum (ssymbTerm "a" :: Term Integer) of
          UMinusNumTerm (_ :: Term (BVU.UnsignedBV 3)) -> expectationFailure "EqvTerm pattern should check type"
          UMinusNumTerm (v1 :: Term Integer) -> do
            v1 `shouldBe` ssymbTerm "a"
          _ -> return ()
  describe "Times" $ do
    describe "Times construction" $ do
      it "Times on both concrete" $ do
        timesNum (concTerm 3 :: Term Integer) (concTerm 5)
          `shouldBe` concTerm 15
      it "Times on left 0" $ do
        timesNum (concTerm 0 :: Term Integer) (ssymbTerm "a")
          `shouldBe` concTerm 0
      it "Times on right 0" $ do
        timesNum (ssymbTerm "a") (concTerm 0 :: Term Integer)
          `shouldBe` concTerm 0
      it "Times on left 1" $ do
        timesNum (concTerm 1 :: Term Integer) (ssymbTerm "a")
          `shouldBe` ssymbTerm "a"
      it "Times on right 1" $ do
        timesNum (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` ssymbTerm "a"
      it "Times on left -1" $ do
        timesNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
          `shouldBe` uminusNum (ssymbTerm "a")
      it "Times on right -1" $ do
        timesNum (ssymbTerm "a") (concTerm $ -1 :: Term Integer)
          `shouldBe` uminusNum (ssymbTerm "a")
      it "Times left concrete right times concrete symbolics" $ do
        timesNum (concTerm 3) (timesNum (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` timesNum (concTerm 15) (ssymbTerm "a")
      it "Times right concrete left times concrete symbolics" $ do
        timesNum (timesNum (concTerm 5 :: Term Integer) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` timesNum (concTerm 15) (ssymbTerm "a")
      it "Times left concrete right add concrete symbolics" $ do
        timesNum (concTerm 3) (addNum (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` addNum (concTerm 15) (timesNum (concTerm 3) (ssymbTerm "a"))
      it "Times right concrete left add concrete symbolics" $ do
        timesNum (addNum (concTerm 5 :: Term Integer) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` addNum (concTerm 15) (timesNum (concTerm 3) (ssymbTerm "a"))
      it "Times left concrete right uminus" $ do
        timesNum (concTerm 3 :: Term Integer) (uminusNum (ssymbTerm "a"))
          `shouldBe` timesNum (concTerm $ -3) (ssymbTerm "a")
      it "Times left times concrete symbolics" $ do
        timesNum (timesNum (concTerm 3 :: Term Integer) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` timesNum (concTerm 3) (timesNum (ssymbTerm "a") (ssymbTerm "b"))
      it "Times right times concrete symbolics" $ do
        timesNum (ssymbTerm "b") (timesNum (concTerm 3 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` timesNum (concTerm 3) (timesNum (ssymbTerm "b") (ssymbTerm "a"))
      it "Times on left uminus" $ do
        timesNum (uminusNum $ ssymbTerm "a") (ssymbTerm "b" :: Term Integer)
          `shouldBe` uminusNum (timesNum (ssymbTerm "a") (ssymbTerm "b"))
      it "Times on right uminus" $ do
        timesNum (ssymbTerm "a") (uminusNum $ ssymbTerm "b" :: Term Integer)
          `shouldBe` uminusNum (timesNum (ssymbTerm "a") (ssymbTerm "b"))
      it "Times right concrete left uminus" $ do
        timesNum (uminusNum (ssymbTerm "a")) (concTerm 3 :: Term Integer)
          `shouldBe` timesNum (concTerm $ -3) (ssymbTerm "a")
      it "Times on left concrete" $ do
        timesNum (concTerm 3 :: Term Integer) (ssymbTerm "a")
          `shouldBe` constructBinary
            TimesNum
            (concTerm 3 :: Term Integer)
            (ssymbTerm "a" :: Term Integer)
      it "Times on right concrete" $ do
        timesNum (ssymbTerm "a") (concTerm 3 :: Term Integer)
          `shouldBe` constructBinary
            TimesNum
            (concTerm 3 :: Term Integer)
            (ssymbTerm "a" :: Term Integer)
      it "Times on no concrete" $ do
        timesNum (ssymbTerm "a") (ssymbTerm "b" :: Term Integer)
          `shouldBe` constructBinary TimesNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
      it "Times unfold 1" $ do
        timesNum
          (concTerm 3)
          (iteterm (ssymbTerm "a") (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` iteterm (ssymbTerm "a") (concTerm 15) (timesNum (concTerm 3) (ssymbTerm "a"))
        timesNum
          (iteterm (ssymbTerm "a") (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          (concTerm 3)
          `shouldBe` iteterm (ssymbTerm "a") (concTerm 15) (timesNum (ssymbTerm "a") (concTerm 3))
    describe "Times pattern" $ do
      it "Times pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          TimesNumTerm (_ :: Term Integer) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case timesNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          TimesNumTerm (_ :: Term (BVU.UnsignedBV 3)) _ -> expectationFailure "EqvTerm pattern should check type"
          TimesNumTerm (v1 :: Term Integer) v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "Abs" $ do
    describe "Abs construction" $ do
      it "Abs on concrete" $ do
        absNum (concTerm 10 :: Term Integer) `shouldBe` concTerm 10
        absNum (concTerm $ -10 :: Term Integer) `shouldBe` concTerm 10
      it "Abs on UMinus" $ do
        absNum (uminusNum $ ssymbTerm "a" :: Term Integer) `shouldBe` absNum (ssymbTerm "a")
      it "Abs on Abs" $ do
        absNum (absNum $ ssymbTerm "a" :: Term Integer) `shouldBe` absNum (ssymbTerm "a")
      it "Abs on Times Integer" $ do
        absNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term Integer)
          `shouldBe` timesNum (absNum (ssymbTerm "a")) (absNum (ssymbTerm "b"))
      it "Abs on Times BV" $ do
        absNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVS.SignedBV 5))
          `shouldBe` constructUnary AbsNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVS.SignedBV 5))
        absNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVU.UnsignedBV 5))
          `shouldBe` constructUnary AbsNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVU.UnsignedBV 5))
      it "Abs symbolic" $ do
        absNum (ssymbTerm "a" :: Term Integer)
          `shouldBe` constructUnary AbsNum (ssymbTerm "a")
    describe "Abs pattern" $ do
      it "Abs pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          AbsNumTerm (_ :: Term Integer) -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case absNum (ssymbTerm "a" :: Term Integer) of
          AbsNumTerm (_ :: Term (BVU.UnsignedBV 3)) -> expectationFailure "EqvTerm pattern should check type"
          AbsNumTerm (v1 :: Term Integer) -> do
            v1 `shouldBe` ssymbTerm "a"
          _ -> return ()
  describe "Signum" $ do
    describe "Signum construction" $ do
      it "Signum on concrete" $ do
        signumNum (concTerm 10 :: Term Integer) `shouldBe` concTerm 1
        signumNum (concTerm 0 :: Term Integer) `shouldBe` concTerm 0
        signumNum (concTerm $ -10 :: Term Integer) `shouldBe` concTerm (-1)
      it "Signum on UMinus Integer" $ do
        signumNum (uminusNum $ ssymbTerm "a" :: Term Integer)
          `shouldBe` uminusNum (signumNum $ ssymbTerm "a")
      it "Signum on UMinus BV" $ do
        signumNum (uminusNum $ ssymbTerm "a" :: Term (BVS.SignedBV 5))
          `shouldBe` constructUnary SignumNum (uminusNum $ ssymbTerm "a" :: Term (BVS.SignedBV 5))
        signumNum (uminusNum $ ssymbTerm "a" :: Term (BVU.UnsignedBV 5))
          `shouldBe` constructUnary SignumNum (uminusNum $ ssymbTerm "a" :: Term (BVU.UnsignedBV 5))
      it "Signum on Times Integer" $ do
        signumNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term Integer)
          `shouldBe` timesNum (signumNum $ ssymbTerm "a") (signumNum $ ssymbTerm "b")
      it "Signum on Times BV" $ do
        signumNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVS.SignedBV 5))
          `shouldBe` constructUnary SignumNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVS.SignedBV 5))
        signumNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVU.UnsignedBV 5))
          `shouldBe` constructUnary SignumNum (timesNum (ssymbTerm "a") (ssymbTerm "b") :: Term (BVU.UnsignedBV 5))
      it "Signum symbolics" $ do
        signumNum (ssymbTerm "a" :: Term Integer)
          `shouldBe` constructUnary SignumNum (ssymbTerm "a")
    describe "Signum pattern" $ do
      it "Signum pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          SignumNumTerm (_ :: Term Integer) -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case signumNum (ssymbTerm "a" :: Term Integer) of
          SignumNumTerm (_ :: Term (BVU.UnsignedBV 3)) -> expectationFailure "EqvTerm pattern should check type"
          SignumNumTerm (v1 :: Term Integer) -> do
            v1 `shouldBe` ssymbTerm "a"
          _ -> return ()
  describe "Lt" $ do
    describe "Lt construction" $ do
      it "Lt on both concrete" $ do
        ltNum (concTerm 1 :: Term Integer) (concTerm 2) `shouldBe` concTerm True
        ltNum (concTerm 2 :: Term Integer) (concTerm 2) `shouldBe` concTerm False
        ltNum (concTerm 3 :: Term Integer) (concTerm 2) `shouldBe` concTerm False
        ltNum (concTerm 1 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm False
        ltNum (concTerm 2 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm True
        ltNum (concTerm 3 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm True
        ltNum (concTerm 1 :: Term (BVU.UnsignedBV 2)) (concTerm 2) `shouldBe` concTerm True
        ltNum (concTerm 2 :: Term (BVU.UnsignedBV 2)) (concTerm 2) `shouldBe` concTerm False
        ltNum (concTerm 3 :: Term (BVU.UnsignedBV 2)) (concTerm 2) `shouldBe` concTerm False
      it "Lt on left constant right add concrete Integers" $ do
        ltNum (concTerm 1 :: Term Integer) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` ltNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Lt on right constant left add concrete Integers" $ do
        ltNum (addNum (concTerm 2) (ssymbTerm "a")) (concTerm 1 :: Term Integer)
          `shouldBe` ltNum (concTerm 1 :: Term Integer) (uminusNum $ ssymbTerm "a")
      it "Lt on right constant Integers" $ do
        ltNum (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` ltNum (concTerm $ -1 :: Term Integer) (uminusNum $ ssymbTerm "a")
      it "Lt on right constant left uminus Integers" $ do
        ltNum (uminusNum $ ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` ltNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Lt on left add concrete Integers" $ do
        ltNum (addNum (concTerm 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term Integer)
          `shouldBe` ltNum (concTerm 2 :: Term Integer) (addNum (ssymbTerm "b") (uminusNum $ ssymbTerm "a"))
      it "Lt on right add concrete Integers" $ do
        ltNum (ssymbTerm "b" :: Term Integer) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` ltNum (concTerm $ -2 :: Term Integer) (addNum (ssymbTerm "a") (uminusNum $ ssymbTerm "b"))
      let concSignedBV :: Integer -> Term (BVS.SignedBV 5) = concTerm . fromInteger
      let concUnsignedBV :: Integer -> Term (BVU.UnsignedBV 5) = concTerm . fromInteger
      it "Lt on left constant right add concrete BVs should not be simplified" $ do
        ltNum (concSignedBV 1) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LTNum (concSignedBV 1) (addNum (concSignedBV 2) (ssymbTerm "a"))
        ltNum (concUnsignedBV 1) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LTNum (concUnsignedBV 1) (addNum (concUnsignedBV 2) (ssymbTerm "a"))
      it "Lt on right constant left add concrete BVs should not be simplified" $ do
        ltNum (addNum (concSignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LTNum (addNum (concSignedBV 2) (ssymbTerm "a")) (concSignedBV 1)
        ltNum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LTNum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (concUnsignedBV 1)
      it "Lt on right constant BVs should not be simplified" $ do
        ltNum (ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LTNum (ssymbTerm "a" :: Term (BVS.SignedBV 5)) (concSignedBV 1)
        ltNum (ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LTNum (ssymbTerm "a" :: Term (BVU.UnsignedBV 5)) (concUnsignedBV 1)
      it "Lt on right constant left uminus BVs should not be simplified" $ do
        ltNum (uminusNum $ ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LTNum (uminusNum $ ssymbTerm "a" :: Term (BVS.SignedBV 5)) (concSignedBV 1)
        ltNum (uminusNum $ ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LTNum (uminusNum $ ssymbTerm "a" :: Term (BVU.UnsignedBV 5)) (concUnsignedBV 1)
      it "Lt on left add concrete BVs should not be simplified" $ do
        ltNum (addNum (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LTNum (addNum (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (BVS.SignedBV 5))
        ltNum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LTNum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (BVU.UnsignedBV 5))
      it "Lt on right add concrete BVs should not be simplified" $ do
        ltNum (ssymbTerm "b") (addNum (concSignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LTNum
            (ssymbTerm "b" :: Term (BVS.SignedBV 5))
            (addNum (concSignedBV 2) (ssymbTerm "a"))
        ltNum (ssymbTerm "b") (addNum (concUnsignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LTNum
            (ssymbTerm "b" :: Term (BVU.UnsignedBV 5))
            (addNum (concUnsignedBV 2) (ssymbTerm "a"))
      it "Lt on symbolic" $ do
        ltNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary LTNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
    describe "Lt pattern" $ do
      it "Lt pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          LTNumTerm (_ :: Term Integer) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case ltNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          LTNumTerm (_ :: Term (BVU.UnsignedBV 3)) _ -> expectationFailure "EqvTerm pattern should check type"
          LTNumTerm (v1 :: Term Integer) v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "Le" $ do
    describe "Le construction" $ do
      it "Le on both concrete" $ do
        leNum (concTerm 1 :: Term Integer) (concTerm 2) `shouldBe` concTerm True
        leNum (concTerm 2 :: Term Integer) (concTerm 2) `shouldBe` concTerm True
        leNum (concTerm 3 :: Term Integer) (concTerm 2) `shouldBe` concTerm False
        leNum (concTerm 0 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm True
        leNum (concTerm 1 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm False
        leNum (concTerm 2 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm True
        leNum (concTerm 3 :: Term (BVS.SignedBV 2)) (concTerm 0) `shouldBe` concTerm True
        leNum (concTerm 1 :: Term (BVU.UnsignedBV 2)) (concTerm 2) `shouldBe` concTerm True
        leNum (concTerm 2 :: Term (BVU.UnsignedBV 2)) (concTerm 2) `shouldBe` concTerm True
        leNum (concTerm 3 :: Term (BVU.UnsignedBV 2)) (concTerm 2) `shouldBe` concTerm False
      it "Le on left constant right add concrete Integers" $ do
        leNum (concTerm 1 :: Term Integer) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` leNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Le on right constant left add concrete Integers" $ do
        leNum (addNum (concTerm 2) (ssymbTerm "a")) (concTerm 1 :: Term Integer)
          `shouldBe` leNum (concTerm 1 :: Term Integer) (uminusNum $ ssymbTerm "a")
      it "Le on right constant Integers" $ do
        leNum (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` leNum (concTerm $ -1 :: Term Integer) (uminusNum $ ssymbTerm "a")
      it "Le on right constant left uminus Integers" $ do
        leNum (uminusNum $ ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` leNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Le on left add concrete Integers" $ do
        leNum (addNum (concTerm 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term Integer)
          `shouldBe` leNum (concTerm 2 :: Term Integer) (addNum (ssymbTerm "b") (uminusNum $ ssymbTerm "a"))
      it "Le on right add concrete Integers" $ do
        leNum (ssymbTerm "b" :: Term Integer) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` leNum (concTerm $ -2 :: Term Integer) (addNum (ssymbTerm "a") (uminusNum $ ssymbTerm "b"))
      let concSignedBV :: Integer -> Term (BVS.SignedBV 5) = concTerm . fromInteger
      let concUnsignedBV :: Integer -> Term (BVU.UnsignedBV 5) = concTerm . fromInteger
      it "Lt on left constant right add concrete BVs should not be simplified" $ do
        leNum (concSignedBV 1) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LENum (concSignedBV 1) (addNum (concSignedBV 2) (ssymbTerm "a"))
        leNum (concUnsignedBV 1) (addNum (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LENum (concUnsignedBV 1) (addNum (concUnsignedBV 2) (ssymbTerm "a"))
      it "Le on right constant left add concrete BVs should not be simplified" $ do
        leNum (addNum (concSignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LENum (addNum (concSignedBV 2) (ssymbTerm "a")) (concSignedBV 1)
        leNum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LENum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (concUnsignedBV 1)
      it "Le on right constant BVs should not be simplified" $ do
        leNum (ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LENum (ssymbTerm "a" :: Term (BVS.SignedBV 5)) (concSignedBV 1)
        leNum (ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LENum (ssymbTerm "a" :: Term (BVU.UnsignedBV 5)) (concUnsignedBV 1)
      it "Le on right constant left uminus BVs should not be simplified" $ do
        leNum (uminusNum $ ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LENum (uminusNum $ ssymbTerm "a" :: Term (BVS.SignedBV 5)) (concSignedBV 1)
        leNum (uminusNum $ ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LENum (uminusNum $ ssymbTerm "a" :: Term (BVU.UnsignedBV 5)) (concUnsignedBV 1)
      it "Le on left add concrete BVs should not be simplified" $ do
        leNum (addNum (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LENum (addNum (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (BVS.SignedBV 5))
        leNum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LENum (addNum (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (BVU.UnsignedBV 5))
      it "Lt on right add concrete BVs should not be simplified" $ do
        leNum (ssymbTerm "b") (addNum (concSignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LENum
            (ssymbTerm "b" :: Term (BVS.SignedBV 5))
            (addNum (concSignedBV 2) (ssymbTerm "a"))
        leNum (ssymbTerm "b") (addNum (concUnsignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LENum
            (ssymbTerm "b" :: Term (BVU.UnsignedBV 5))
            (addNum (concUnsignedBV 2) (ssymbTerm "a"))
      it "Le on symbolic" $ do
        leNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary LENum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
    describe "Le pattern" $ do
      it "Le pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          LENumTerm (_ :: Term Integer) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case leNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          LENumTerm (_ :: Term (BVU.UnsignedBV 3)) _ -> expectationFailure "EqvTerm pattern should check type"
          LENumTerm (v1 :: Term Integer) v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "Gt" $ do
    it "Gt should be delegated to Lt" $ do
      gtNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
        `shouldBe` ltNum (ssymbTerm "b" :: Term Integer) (ssymbTerm "a")
  describe "Ge" $ do
    it "Ge should be delegated to Le" $ do
      geNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
        `shouldBe` leNum (ssymbTerm "b" :: Term Integer) (ssymbTerm "a")