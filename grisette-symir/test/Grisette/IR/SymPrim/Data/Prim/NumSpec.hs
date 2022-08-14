{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.IR.SymPrim.Data.Prim.NumSpec where

import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.Num
import Test.Hspec

spec :: Spec
spec = do
  describe "Add" $ do
    describe "Add construction" $ do
      it "Add on concrete" $ do
        pevalAddNumTerm (concTerm 1 :: Term Integer) (concTerm 2) `shouldBe` concTerm 3
        pevalAddNumTerm (concTerm 1 :: Term (WordN 3)) (concTerm 2) `shouldBe` concTerm 3
        pevalAddNumTerm (concTerm 1 :: Term (IntN 3)) (concTerm 2) `shouldBe` concTerm 3
      it "Add on left 0" $ do
        pevalAddNumTerm (concTerm 0 :: Term Integer) (ssymbTerm "a") `shouldBe` ssymbTerm "a"
      it "Add on right 0" $ do
        pevalAddNumTerm (ssymbTerm "a") (concTerm 0 :: Term Integer) `shouldBe` ssymbTerm "a"
      it "Add on left concrete" $ do
        pevalAddNumTerm (concTerm 1 :: Term Integer) (ssymbTerm "a")
          `shouldBe` addNumTerm (concTerm 1 :: Term Integer) (ssymbTerm "a" :: Term Integer)
      it "Add on right concrete" $ do
        pevalAddNumTerm (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` addNumTerm (concTerm 1 :: Term Integer) (ssymbTerm "a" :: Term Integer)
      it "Add on no concrete" $ do
        pevalAddNumTerm (ssymbTerm "a") (ssymbTerm "b" :: Term Integer)
          `shouldBe` addNumTerm (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
      it "Add when left concrete right add concrete value" $ do
        pevalAddNumTerm (concTerm 1 :: Term Integer) (pevalAddNumTerm (concTerm 2 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalAddNumTerm (concTerm 3 :: Term Integer) (ssymbTerm "a")
      it "Add when right concrete left add concrete value" $ do
        pevalAddNumTerm (pevalAddNumTerm (concTerm 2 :: Term Integer) (ssymbTerm "a")) (concTerm 1 :: Term Integer)
          `shouldBe` pevalAddNumTerm (concTerm 3 :: Term Integer) (ssymbTerm "a")
      it "Add when left add concrete" $ do
        pevalAddNumTerm (pevalAddNumTerm (concTerm 2 :: Term Integer) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` pevalAddNumTerm (concTerm 2 :: Term Integer) (pevalAddNumTerm (ssymbTerm "a") (ssymbTerm "b"))
      it "Add when right add concrete" $ do
        pevalAddNumTerm (ssymbTerm "b") (pevalAddNumTerm (concTerm 2 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalAddNumTerm (concTerm 2 :: Term Integer) (pevalAddNumTerm (ssymbTerm "b") (ssymbTerm "a"))
      it "Add when both uminus" $ do
        pevalAddNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term Integer) (pevalUMinusNumTerm $ ssymbTerm "b")
          `shouldBe` pevalUMinusNumTerm (pevalAddNumTerm (ssymbTerm "a") (ssymbTerm "b"))
      it "Add when both times the same concrete" $ do
        pevalAddNumTerm
          (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a") :: Term Integer)
          (pevalTimesNumTerm (concTerm 3) (ssymbTerm "b"))
          `shouldBe` pevalTimesNumTerm (concTerm 3) (pevalAddNumTerm (ssymbTerm "a") (ssymbTerm "b"))
      it "Add when both times the same symbolic" $ do
        pevalAddNumTerm
          (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a") :: Term Integer)
          (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a"))
          `shouldBe` pevalTimesNumTerm (concTerm 6) (ssymbTerm "a")
        pevalAddNumTerm
          (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a") :: Term Integer)
          (pevalTimesNumTerm (concTerm 4) (ssymbTerm "a"))
          `shouldBe` pevalTimesNumTerm (concTerm 7) (ssymbTerm "a")
      it "Add unfold 1" $ do
        pevalAddNumTerm
          (concTerm 3)
          (pevalITETerm (ssymbTerm "a") (concTerm 1 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalITETerm (ssymbTerm "a") (concTerm 4) (pevalAddNumTerm (concTerm 3) (ssymbTerm "a"))
        pevalAddNumTerm
          (pevalITETerm (ssymbTerm "a") (concTerm 1 :: Term Integer) (ssymbTerm "a"))
          (concTerm 3)
          `shouldBe` pevalITETerm (ssymbTerm "a") (concTerm 4) (pevalAddNumTerm (ssymbTerm "a") (concTerm 3))
  describe "minus" $ do
    it "minus num should be delegated to add and uminus" $ do
      pevalMinusNumTerm (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
        `shouldBe` pevalAddNumTerm (ssymbTerm "a") (pevalUMinusNumTerm $ ssymbTerm "b")
  describe "UMinus" $ do
    describe "UMinus construction" $ do
      it "UMinus on concrete" $ do
        pevalUMinusNumTerm (concTerm 1 :: Term Integer) `shouldBe` concTerm (-1)
        pevalUMinusNumTerm (concTerm 1 :: Term (WordN 3)) `shouldBe` concTerm (-1)
      it "UMinus on UMinus" $ do
        pevalUMinusNumTerm (pevalUMinusNumTerm (ssymbTerm "a" :: Term Integer)) `shouldBe` ssymbTerm "a"
      it "UMinus on Add concrete" $ do
        pevalUMinusNumTerm (pevalAddNumTerm (concTerm 1) (ssymbTerm "a" :: Term Integer))
          `shouldBe` pevalAddNumTerm (concTerm $ -1) (pevalUMinusNumTerm $ ssymbTerm "a")
      it "UMinus on Add uminus" $ do
        pevalUMinusNumTerm (pevalAddNumTerm (pevalUMinusNumTerm $ ssymbTerm "a") (ssymbTerm "b" :: Term Integer))
          `shouldBe` pevalAddNumTerm (ssymbTerm "a") (pevalUMinusNumTerm $ ssymbTerm "b")
        pevalUMinusNumTerm (pevalAddNumTerm (ssymbTerm "a") (pevalUMinusNumTerm $ ssymbTerm "b" :: Term Integer))
          `shouldBe` pevalAddNumTerm (pevalUMinusNumTerm $ ssymbTerm "a") (ssymbTerm "b")
      it "UMinus on Times concrete" $ do
        pevalUMinusNumTerm (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a" :: Term Integer))
          `shouldBe` pevalTimesNumTerm (concTerm $ -3) (ssymbTerm "a")
      it "UMinus symbolic" $ do
        pevalUMinusNumTerm (ssymbTerm "a" :: Term Integer)
          `shouldBe` uminusNumTerm (ssymbTerm "a")
  describe "Times" $ do
    describe "Times construction" $ do
      it "Times on both concrete" $ do
        pevalTimesNumTerm (concTerm 3 :: Term Integer) (concTerm 5)
          `shouldBe` concTerm 15
      it "Times on left 0" $ do
        pevalTimesNumTerm (concTerm 0 :: Term Integer) (ssymbTerm "a")
          `shouldBe` concTerm 0
      it "Times on right 0" $ do
        pevalTimesNumTerm (ssymbTerm "a") (concTerm 0 :: Term Integer)
          `shouldBe` concTerm 0
      it "Times on left 1" $ do
        pevalTimesNumTerm (concTerm 1 :: Term Integer) (ssymbTerm "a")
          `shouldBe` ssymbTerm "a"
      it "Times on right 1" $ do
        pevalTimesNumTerm (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` ssymbTerm "a"
      it "Times on left -1" $ do
        pevalTimesNumTerm (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
          `shouldBe` pevalUMinusNumTerm (ssymbTerm "a")
      it "Times on right -1" $ do
        pevalTimesNumTerm (ssymbTerm "a") (concTerm $ -1 :: Term Integer)
          `shouldBe` pevalUMinusNumTerm (ssymbTerm "a")
      it "Times left concrete right times concrete symbolics" $ do
        pevalTimesNumTerm (concTerm 3) (pevalTimesNumTerm (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalTimesNumTerm (concTerm 15) (ssymbTerm "a")
      it "Times right concrete left times concrete symbolics" $ do
        pevalTimesNumTerm (pevalTimesNumTerm (concTerm 5 :: Term Integer) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` pevalTimesNumTerm (concTerm 15) (ssymbTerm "a")
      it "Times left concrete right add concrete symbolics" $ do
        pevalTimesNumTerm (concTerm 3) (pevalAddNumTerm (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalAddNumTerm (concTerm 15) (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a"))
      it "Times right concrete left add concrete symbolics" $ do
        pevalTimesNumTerm (pevalAddNumTerm (concTerm 5 :: Term Integer) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` pevalAddNumTerm (concTerm 15) (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a"))
      it "Times left concrete right uminus" $ do
        pevalTimesNumTerm (concTerm 3 :: Term Integer) (pevalUMinusNumTerm (ssymbTerm "a"))
          `shouldBe` pevalTimesNumTerm (concTerm $ -3) (ssymbTerm "a")
      it "Times left times concrete symbolics" $ do
        pevalTimesNumTerm (pevalTimesNumTerm (concTerm 3 :: Term Integer) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` pevalTimesNumTerm (concTerm 3) (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b"))
      it "Times right times concrete symbolics" $ do
        pevalTimesNumTerm (ssymbTerm "b") (pevalTimesNumTerm (concTerm 3 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalTimesNumTerm (concTerm 3) (pevalTimesNumTerm (ssymbTerm "b") (ssymbTerm "a"))
      it "Times on left uminus" $ do
        pevalTimesNumTerm (pevalUMinusNumTerm $ ssymbTerm "a") (ssymbTerm "b" :: Term Integer)
          `shouldBe` pevalUMinusNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b"))
      it "Times on right uminus" $ do
        pevalTimesNumTerm (ssymbTerm "a") (pevalUMinusNumTerm $ ssymbTerm "b" :: Term Integer)
          `shouldBe` pevalUMinusNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b"))
      it "Times right concrete left uminus" $ do
        pevalTimesNumTerm (pevalUMinusNumTerm (ssymbTerm "a")) (concTerm 3 :: Term Integer)
          `shouldBe` pevalTimesNumTerm (concTerm $ -3) (ssymbTerm "a")
      it "Times on left concrete" $ do
        pevalTimesNumTerm (concTerm 3 :: Term Integer) (ssymbTerm "a")
          `shouldBe` timesNumTerm
            (concTerm 3 :: Term Integer)
            (ssymbTerm "a" :: Term Integer)
      it "Times on right concrete" $ do
        pevalTimesNumTerm (ssymbTerm "a") (concTerm 3 :: Term Integer)
          `shouldBe` timesNumTerm
            (concTerm 3 :: Term Integer)
            (ssymbTerm "a" :: Term Integer)
      it "Times on no concrete" $ do
        pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b" :: Term Integer)
          `shouldBe` timesNumTerm (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
      it "Times unfold 1" $ do
        pevalTimesNumTerm
          (concTerm 3)
          (pevalITETerm (ssymbTerm "a") (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` pevalITETerm (ssymbTerm "a") (concTerm 15) (pevalTimesNumTerm (concTerm 3) (ssymbTerm "a"))
        pevalTimesNumTerm
          (pevalITETerm (ssymbTerm "a") (concTerm 5 :: Term Integer) (ssymbTerm "a"))
          (concTerm 3)
          `shouldBe` pevalITETerm (ssymbTerm "a") (concTerm 15) (pevalTimesNumTerm (ssymbTerm "a") (concTerm 3))
  describe "Abs" $ do
    describe "Abs construction" $ do
      it "Abs on concrete" $ do
        pevalAbsNumTerm (concTerm 10 :: Term Integer) `shouldBe` concTerm 10
        pevalAbsNumTerm (concTerm $ -10 :: Term Integer) `shouldBe` concTerm 10
      it "Abs on UMinus" $ do
        pevalAbsNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term Integer) `shouldBe` pevalAbsNumTerm (ssymbTerm "a")
      it "Abs on Abs" $ do
        pevalAbsNumTerm (pevalAbsNumTerm $ ssymbTerm "a" :: Term Integer) `shouldBe` pevalAbsNumTerm (ssymbTerm "a")
      it "Abs on Times Integer" $ do
        pevalAbsNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term Integer)
          `shouldBe` pevalTimesNumTerm (pevalAbsNumTerm (ssymbTerm "a")) (pevalAbsNumTerm (ssymbTerm "b"))
      it "Abs on Times BV" $ do
        pevalAbsNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (IntN 5))
          `shouldBe` absNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (IntN 5))
        pevalAbsNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (WordN 5))
          `shouldBe` absNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (WordN 5))
      it "Abs symbolic" $ do
        pevalAbsNumTerm (ssymbTerm "a" :: Term Integer)
          `shouldBe` absNumTerm (ssymbTerm "a")
  describe "Signum" $ do
    describe "Signum construction" $ do
      it "Signum on concrete" $ do
        pevalSignumNumTerm (concTerm 10 :: Term Integer) `shouldBe` concTerm 1
        pevalSignumNumTerm (concTerm 0 :: Term Integer) `shouldBe` concTerm 0
        pevalSignumNumTerm (concTerm $ -10 :: Term Integer) `shouldBe` concTerm (-1)
      it "Signum on UMinus Integer" $ do
        pevalSignumNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term Integer)
          `shouldBe` pevalUMinusNumTerm (pevalSignumNumTerm $ ssymbTerm "a")
      it "Signum on UMinus BV" $ do
        pevalSignumNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (IntN 5))
          `shouldBe` signumNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (IntN 5))
        pevalSignumNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (WordN 5))
          `shouldBe` signumNumTerm (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (WordN 5))
      it "Signum on Times Integer" $ do
        pevalSignumNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term Integer)
          `shouldBe` pevalTimesNumTerm (pevalSignumNumTerm $ ssymbTerm "a") (pevalSignumNumTerm $ ssymbTerm "b")
      it "Signum on Times BV" $ do
        pevalSignumNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (IntN 5))
          `shouldBe` signumNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (IntN 5))
        pevalSignumNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (WordN 5))
          `shouldBe` signumNumTerm (pevalTimesNumTerm (ssymbTerm "a") (ssymbTerm "b") :: Term (WordN 5))
      it "Signum symbolics" $ do
        pevalSignumNumTerm (ssymbTerm "a" :: Term Integer)
          `shouldBe` signumNumTerm (ssymbTerm "a")
  describe "Lt" $ do
    describe "Lt construction" $ do
      it "Lt on both concrete" $ do
        ltNum (concTerm 1 :: Term Integer) (concTerm 2) `shouldBe` concTerm True
        ltNum (concTerm 2 :: Term Integer) (concTerm 2) `shouldBe` concTerm False
        ltNum (concTerm 3 :: Term Integer) (concTerm 2) `shouldBe` concTerm False
        ltNum (concTerm 1 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm False
        ltNum (concTerm 2 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm True
        ltNum (concTerm 3 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm True
        ltNum (concTerm 1 :: Term (WordN 2)) (concTerm 2) `shouldBe` concTerm True
        ltNum (concTerm 2 :: Term (WordN 2)) (concTerm 2) `shouldBe` concTerm False
        ltNum (concTerm 3 :: Term (WordN 2)) (concTerm 2) `shouldBe` concTerm False
      it "Lt on left constant right add concrete Integers" $ do
        ltNum (concTerm 1 :: Term Integer) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` ltNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Lt on right constant left add concrete Integers" $ do
        ltNum (pevalAddNumTerm (concTerm 2) (ssymbTerm "a")) (concTerm 1 :: Term Integer)
          `shouldBe` ltNum (concTerm 1 :: Term Integer) (pevalUMinusNumTerm $ ssymbTerm "a")
      it "Lt on right constant Integers" $ do
        ltNum (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` ltNum (concTerm $ -1 :: Term Integer) (pevalUMinusNumTerm $ ssymbTerm "a")
      it "Lt on right constant left uminus Integers" $ do
        ltNum (pevalUMinusNumTerm $ ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` ltNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Lt on left add concrete Integers" $ do
        ltNum (pevalAddNumTerm (concTerm 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term Integer)
          `shouldBe` ltNum (concTerm 2 :: Term Integer) (pevalAddNumTerm (ssymbTerm "b") (pevalUMinusNumTerm $ ssymbTerm "a"))
      it "Lt on right add concrete Integers" $ do
        ltNum (ssymbTerm "b" :: Term Integer) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` ltNum (concTerm $ -2 :: Term Integer) (pevalAddNumTerm (ssymbTerm "a") (pevalUMinusNumTerm $ ssymbTerm "b"))
      let concSignedBV :: Integer -> Term (IntN 5) = concTerm . fromInteger
      let concUnsignedBV :: Integer -> Term (WordN 5) = concTerm . fromInteger
      it "Lt on left constant right add concrete BVs should not be simplified" $ do
        ltNum (concSignedBV 1) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LTNum (concSignedBV 1) (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a"))
        ltNum (concUnsignedBV 1) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LTNum (concUnsignedBV 1) (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a"))
      it "Lt on right constant left add concrete BVs should not be simplified" $ do
        ltNum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LTNum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (concSignedBV 1)
        ltNum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LTNum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (concUnsignedBV 1)
      it "Lt on right constant BVs should not be simplified" $ do
        ltNum (ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LTNum (ssymbTerm "a" :: Term (IntN 5)) (concSignedBV 1)
        ltNum (ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LTNum (ssymbTerm "a" :: Term (WordN 5)) (concUnsignedBV 1)
      it "Lt on right constant left uminus BVs should not be simplified" $ do
        ltNum (pevalUMinusNumTerm $ ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LTNum (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (IntN 5)) (concSignedBV 1)
        ltNum (pevalUMinusNumTerm $ ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LTNum (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (WordN 5)) (concUnsignedBV 1)
      it "Lt on left add concrete BVs should not be simplified" $ do
        ltNum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LTNum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (IntN 5))
        ltNum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LTNum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (WordN 5))
      it "Lt on right add concrete BVs should not be simplified" $ do
        ltNum (ssymbTerm "b") (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LTNum
            (ssymbTerm "b" :: Term (IntN 5))
            (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a"))
        ltNum (ssymbTerm "b") (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LTNum
            (ssymbTerm "b" :: Term (WordN 5))
            (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a"))
      it "Lt on symbolic" $ do
        ltNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary LTNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
    describe "Lt pattern" $ do
      it "Lt pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          LTNumTerm (_ :: Term Integer) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case ltNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          LTNumTerm (_ :: Term (WordN 3)) _ -> expectationFailure "EqvTerm pattern should check type"
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
        leNum (concTerm 0 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm True
        leNum (concTerm 1 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm False
        leNum (concTerm 2 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm True
        leNum (concTerm 3 :: Term (IntN 2)) (concTerm 0) `shouldBe` concTerm True
        leNum (concTerm 1 :: Term (WordN 2)) (concTerm 2) `shouldBe` concTerm True
        leNum (concTerm 2 :: Term (WordN 2)) (concTerm 2) `shouldBe` concTerm True
        leNum (concTerm 3 :: Term (WordN 2)) (concTerm 2) `shouldBe` concTerm False
      it "Le on left constant right add concrete Integers" $ do
        leNum (concTerm 1 :: Term Integer) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` leNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Le on right constant left add concrete Integers" $ do
        leNum (pevalAddNumTerm (concTerm 2) (ssymbTerm "a")) (concTerm 1 :: Term Integer)
          `shouldBe` leNum (concTerm 1 :: Term Integer) (pevalUMinusNumTerm $ ssymbTerm "a")
      it "Le on right constant Integers" $ do
        leNum (ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` leNum (concTerm $ -1 :: Term Integer) (pevalUMinusNumTerm $ ssymbTerm "a")
      it "Le on right constant left uminus Integers" $ do
        leNum (pevalUMinusNumTerm $ ssymbTerm "a") (concTerm 1 :: Term Integer)
          `shouldBe` leNum (concTerm $ -1 :: Term Integer) (ssymbTerm "a")
      it "Le on left add concrete Integers" $ do
        leNum (pevalAddNumTerm (concTerm 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term Integer)
          `shouldBe` leNum (concTerm 2 :: Term Integer) (pevalAddNumTerm (ssymbTerm "b") (pevalUMinusNumTerm $ ssymbTerm "a"))
      it "Le on right add concrete Integers" $ do
        leNum (ssymbTerm "b" :: Term Integer) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` leNum (concTerm $ -2 :: Term Integer) (pevalAddNumTerm (ssymbTerm "a") (pevalUMinusNumTerm $ ssymbTerm "b"))
      let concSignedBV :: Integer -> Term (IntN 5) = concTerm . fromInteger
      let concUnsignedBV :: Integer -> Term (WordN 5) = concTerm . fromInteger
      it "Lt on left constant right add concrete BVs should not be simplified" $ do
        leNum (concSignedBV 1) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LENum (concSignedBV 1) (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a"))
        leNum (concUnsignedBV 1) (pevalAddNumTerm (concTerm 2) (ssymbTerm "a"))
          `shouldBe` constructBinary LENum (concUnsignedBV 1) (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a"))
      it "Le on right constant left add concrete BVs should not be simplified" $ do
        leNum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LENum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (concSignedBV 1)
        leNum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (concTerm 1)
          `shouldBe` constructBinary LENum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (concUnsignedBV 1)
      it "Le on right constant BVs should not be simplified" $ do
        leNum (ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LENum (ssymbTerm "a" :: Term (IntN 5)) (concSignedBV 1)
        leNum (ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LENum (ssymbTerm "a" :: Term (WordN 5)) (concUnsignedBV 1)
      it "Le on right constant left uminus BVs should not be simplified" $ do
        leNum (pevalUMinusNumTerm $ ssymbTerm "a") (concSignedBV 1)
          `shouldBe` constructBinary LENum (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (IntN 5)) (concSignedBV 1)
        leNum (pevalUMinusNumTerm $ ssymbTerm "a") (concUnsignedBV 1)
          `shouldBe` constructBinary LENum (pevalUMinusNumTerm $ ssymbTerm "a" :: Term (WordN 5)) (concUnsignedBV 1)
      it "Le on left add concrete BVs should not be simplified" $ do
        leNum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LENum (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (IntN 5))
        leNum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` constructBinary LENum (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a")) (ssymbTerm "b" :: Term (WordN 5))
      it "Lt on right add concrete BVs should not be simplified" $ do
        leNum (ssymbTerm "b") (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LENum
            (ssymbTerm "b" :: Term (IntN 5))
            (pevalAddNumTerm (concSignedBV 2) (ssymbTerm "a"))
        leNum (ssymbTerm "b") (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a"))
          `shouldBe` constructBinary
            LENum
            (ssymbTerm "b" :: Term (WordN 5))
            (pevalAddNumTerm (concUnsignedBV 2) (ssymbTerm "a"))
      it "Le on symbolic" $ do
        leNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary LENum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
    describe "Le pattern" $ do
      it "Le pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          LENumTerm (_ :: Term Integer) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case leNum (ssymbTerm "a" :: Term Integer) (ssymbTerm "b") of
          LENumTerm (_ :: Term (WordN 3)) _ -> expectationFailure "EqvTerm pattern should check type"
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