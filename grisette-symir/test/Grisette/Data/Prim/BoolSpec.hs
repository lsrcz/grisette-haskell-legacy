{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Grisette.Data.Prim.BoolSpec where

import Data.BitVector.Sized.Signed as BVS
import Data.BitVector.Sized.Unsigned as BVU
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Num
import Test.Hspec

spec :: Spec
spec = do
  describe "Not" $ do
    describe "Not construction" $ do
      it "Not on concrete" $ do
        notb (concTerm True) `shouldBe` concTerm False
        notb (concTerm True) `shouldBe` concTerm False
      it "Not on general symbolic" $ do
        notb (ssymbTerm "a") `shouldBe` constructUnary Not (ssymbTerm "a" :: Term Bool)
      it "Not on Not" $ do
        notb (notb (ssymbTerm "a")) `shouldBe` ssymbTerm "a"
      it "Not on Or Not" $ do
        notb (orb (notb (ssymbTerm "a")) (ssymbTerm "b"))
          `shouldBe` andb (ssymbTerm "a") (notb (ssymbTerm "b"))
        notb (orb (ssymbTerm "a") (notb (ssymbTerm "b")))
          `shouldBe` andb (notb (ssymbTerm "a")) (ssymbTerm "b")
      it "Not on And Not" $ do
        notb (andb (notb (ssymbTerm "a")) (ssymbTerm "b"))
          `shouldBe` orb (ssymbTerm "a") (notb (ssymbTerm "b"))
        notb (andb (ssymbTerm "a") (notb (ssymbTerm "b")))
          `shouldBe` orb (notb (ssymbTerm "a")) (ssymbTerm "b")
    describe "Not pattern" $ do
      it "Not pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          NotTerm _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case notb (ssymbTerm "a" :: Term Bool) of
          NotTerm v -> v `shouldBe` ssymbTerm "a"
          _ -> return ()
  describe "Eqv & NEqv" $ do
    describe "Eqv construction" $ do
      it "Eqv with both concrete" $ do
        eqterm (concTerm True) (concTerm True) `shouldBe` concTerm True
        eqterm (concTerm True) (concTerm False) `shouldBe` concTerm False
        eqterm (concTerm False) (concTerm True) `shouldBe` concTerm False
        eqterm (concTerm False) (concTerm False) `shouldBe` concTerm True
        eqterm (concTerm (1 :: Integer)) (concTerm 1) `shouldBe` concTerm True
        eqterm (concTerm (1 :: Integer)) (concTerm 2) `shouldBe` concTerm False
        eqterm (concTerm (1 :: BVS.SignedBV 4)) (concTerm 1) `shouldBe` concTerm True
        eqterm (concTerm (1 :: BVS.SignedBV 4)) (concTerm 2) `shouldBe` concTerm False
        eqterm (concTerm (1 :: BVU.UnsignedBV 4)) (concTerm 1) `shouldBe` concTerm True
        eqterm (concTerm (1 :: BVU.UnsignedBV 4)) (concTerm 2) `shouldBe` concTerm False
      it "Eqv with single concrete always put concrete ones in the right" $ do
        eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
          `shouldBe` constructBinary Eqv (ssymbTerm "a" :: Term Integer) (concTerm 1 :: Term Integer)
        eqterm (concTerm 1) (ssymbTerm "a" :: Term Integer)
          `shouldBe` constructBinary Eqv (ssymbTerm "a" :: Term Integer) (concTerm 1 :: Term Integer)
      it "Eqv on general symbolic" $ do
        eqterm (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` constructBinary Eqv (ssymbTerm "a" :: Term Integer) (ssymbTerm "b" :: Term Integer)
      it "Eqv on Bool with single concrete" $ do
        eqterm (concTerm True) (ssymbTerm "a") `shouldBe` ssymbTerm "a"
        eqterm (ssymbTerm "a") (concTerm True) `shouldBe` ssymbTerm "a"
        eqterm (concTerm False) (ssymbTerm "a") `shouldBe` notb (ssymbTerm "a")
        eqterm (ssymbTerm "a") (concTerm False) `shouldBe` notb (ssymbTerm "a")
      it "NEqv on general symbolic" $ do
        neterm (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` notb (eqterm (ssymbTerm "a" :: Term Integer) (ssymbTerm "b"))
      it "Eqv(Not(x), x) / Eqv(x, Not(x))" $ do
        eqterm (notb (ssymbTerm "a")) (ssymbTerm "a") `shouldBe` concTerm False
        eqterm (ssymbTerm "a") (notb (ssymbTerm "a")) `shouldBe` concTerm False
      it "Eqv(n1+x, n2)" $ do
        eqterm (addNum (concTerm 1 :: Term Integer) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` eqterm (ssymbTerm "a") (concTerm 2 :: Term Integer)
        eqterm (addNum (concTerm 1 :: Term (BVS.SignedBV 4)) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` eqterm (ssymbTerm "a") (concTerm 2 :: Term (BVS.SignedBV 4))
        eqterm (addNum (concTerm 1 :: Term (BVU.UnsignedBV 4)) (ssymbTerm "a")) (concTerm 3)
          `shouldBe` eqterm (ssymbTerm "a") (concTerm 2 :: Term (BVU.UnsignedBV 4))
      it "Eqv(n1, n2+x)" $ do
        eqterm (concTerm 3) (addNum (concTerm 1 :: Term Integer) (ssymbTerm "a"))
          `shouldBe` eqterm (ssymbTerm "a") (concTerm 2 :: Term Integer)
        eqterm (concTerm 3) (addNum (concTerm 1 :: Term (BVS.SignedBV 4)) (ssymbTerm "a"))
          `shouldBe` eqterm (ssymbTerm "a") (concTerm 2 :: Term (BVS.SignedBV 4))
        eqterm (concTerm 3) (addNum (concTerm 1 :: Term (BVU.UnsignedBV 4)) (ssymbTerm "a"))
          `shouldBe` eqterm (ssymbTerm "a") (concTerm 2 :: Term (BVU.UnsignedBV 4))
      it "Eqv(l, ITE(c, l, f)) / Eqv(l, ITE(c, t, l) / Eqv(ITE(c, r, f), r) / Eqv(ITE(c, t, r), r)" $ do
        eqterm (ssymbTerm "a" :: Term Integer) (iteterm (ssymbTerm "b") (ssymbTerm "a") (ssymbTerm "c"))
          `shouldBe` orb (ssymbTerm "b") (eqterm (ssymbTerm "a") (ssymbTerm "c" :: Term Integer))
        eqterm (ssymbTerm "a" :: Term Integer) (iteterm (ssymbTerm "b") (ssymbTerm "c") (ssymbTerm "a"))
          `shouldBe` orb (notb $ ssymbTerm "b") (eqterm (ssymbTerm "a") (ssymbTerm "c" :: Term Integer))
        eqterm (iteterm (ssymbTerm "b") (ssymbTerm "a") (ssymbTerm "c")) (ssymbTerm "a" :: Term Integer)
          `shouldBe` orb (ssymbTerm "b") (eqterm (ssymbTerm "c") (ssymbTerm "a" :: Term Integer))
        eqterm (iteterm (ssymbTerm "b") (ssymbTerm "c") (ssymbTerm "a")) (ssymbTerm "a" :: Term Integer)
          `shouldBe` orb (notb $ ssymbTerm "b") (eqterm (ssymbTerm "c") (ssymbTerm "a" :: Term Integer))
    describe "Eqv pattern" $ do
      it "Eqv pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          EqvTerm (_ :: Term Bool) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case eqterm (ssymbTerm "a" :: Term Bool) (ssymbTerm "b") of
          EqvTerm (_ :: Term Integer) _ -> expectationFailure "EqvTerm pattern should check type"
          EqvTerm (v1 :: Term Bool) v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "Or" $ do
    describe "Or construction" $ do
      it "Or with both concrete" $ do
        orb (concTerm True) (concTerm True) `shouldBe` concTerm True
        orb (concTerm True) (concTerm False) `shouldBe` concTerm True
        orb (concTerm False) (concTerm True) `shouldBe` concTerm True
        orb (concTerm False) (concTerm False) `shouldBe` concTerm False
      it "Or on general symbolic" $ do
        orb (ssymbTerm "a") (ssymbTerm "b")
          `shouldBe` constructBinary Or (ssymbTerm "a" :: Term Bool) (ssymbTerm "b" :: Term Bool)
      it "Or(x, y) -> True" $ do
        orb (concTerm True) (ssymbTerm "b") `shouldBe` concTerm True
        orb (ssymbTerm "a") (concTerm True) `shouldBe` concTerm True
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` concTerm True
        orb (notb (ssymbTerm "a")) (ssymbTerm "a") `shouldBe` concTerm True
        orb (ssymbTerm "a") (notb (ssymbTerm "a")) `shouldBe` concTerm True
      it "Or(x, y) -> x" $ do
        orb (ssymbTerm "a") (concTerm False) `shouldBe` ssymbTerm "a"
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
        orb (ssymbTerm "a") (ssymbTerm "a") `shouldBe` ssymbTerm "a"
      it "Or(x, y) -> y" $ do
        orb (concTerm False) (ssymbTerm "a") `shouldBe` ssymbTerm "a"
        orb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
      it "Or(x, Or(y1, y2)) -> True" $ do
        orb (notb (ssymbTerm "a")) (orb (ssymbTerm "a") (ssymbTerm "b")) `shouldBe` concTerm True
        orb (ssymbTerm "a") (orb (notb (ssymbTerm "a")) (ssymbTerm "b")) `shouldBe` concTerm True
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` concTerm True

        orb (notb (ssymbTerm "a")) (orb (ssymbTerm "b") (ssymbTerm "a")) `shouldBe` concTerm True
        orb (ssymbTerm "a") (orb (ssymbTerm "b") (notb (ssymbTerm "a"))) `shouldBe` concTerm True
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` concTerm True
      it "Or(x, Or(y1, y2)) -> Or(x, y2)" $ do
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "Or(x, Or(y1, y2)) -> Or(x, y1)" $ do
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")

      it "Or(x, y@Or(y1, y2)) -> y" $ do
        orb (ssymbTerm "a") (orb (ssymbTerm "a") (ssymbTerm "b"))
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "b")
        orb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b"))
          `shouldBe` orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
        orb (ssymbTerm "a") (orb (ssymbTerm "b") (ssymbTerm "a"))
          `shouldBe` orb (ssymbTerm "b") (ssymbTerm "a")
        orb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)))
          `shouldBe` orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "Or(Or(x1, x2), y) -> True" $ do
        orb (orb (ssymbTerm "a") (ssymbTerm "b")) (notb (ssymbTerm "a")) `shouldBe` concTerm True
        orb (orb (notb (ssymbTerm "a")) (ssymbTerm "b")) (ssymbTerm "a") `shouldBe` concTerm True
        orb
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` concTerm True

        orb (orb (ssymbTerm "b") (ssymbTerm "a")) (notb (ssymbTerm "a")) `shouldBe` concTerm True
        orb (orb (ssymbTerm "b") (notb (ssymbTerm "a"))) (ssymbTerm "a") `shouldBe` concTerm True
        orb
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` concTerm True
      it "Or(x@Or(x1, x2), y) -> x" $ do
        orb (orb (ssymbTerm "a") (ssymbTerm "b")) (ssymbTerm "a")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "b")
        orb
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b"))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
        orb (orb (ssymbTerm "b") (ssymbTerm "a")) (ssymbTerm "a")
          `shouldBe` orb (ssymbTerm "b") (ssymbTerm "a")
        orb
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "Or(Or(x1, x2), y) -> Or(x2, y)" $ do
        orb
          (orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "Or(Or(x1, x2), y) -> Or(x1, y)" $ do
        orb
          (orb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "Or(x, And(y1, y2)) -> x" $ do
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
      it "Or(x, And(y1, y2)) -> Or(x, y2)" $ do
        orb (ssymbTerm "a") (andb (notb (ssymbTerm "a")) (ssymbTerm "b"))
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "b")
        orb (notb (ssymbTerm "a")) (andb (ssymbTerm "a") (ssymbTerm "b"))
          `shouldBe` orb (notb (ssymbTerm "a")) (ssymbTerm "b")
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "Or(And(x1, x2), y) -> y" $ do
        orb
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
        orb
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
      it "Or(x, And(y1, y2)) -> Or(x, y1)" $ do
        orb (ssymbTerm "a") (andb (ssymbTerm "b") (notb (ssymbTerm "a")))
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "b")
        orb (notb (ssymbTerm "a")) (andb (ssymbTerm "b") (ssymbTerm "a"))
          `shouldBe` orb (notb (ssymbTerm "a")) (ssymbTerm "b")
        orb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "Or(Not(x), Not(y)) -> Not(And(x, y))" $ do
        orb (notb (ssymbTerm "a")) (notb (ssymbTerm "b"))
          `shouldBe` notb (andb (ssymbTerm "a") (ssymbTerm "b"))
    describe "Or pattern" $ do
      it "Or pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          OrTerm (_ :: Term Bool) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case orb (ssymbTerm "a" :: Term Bool) (ssymbTerm "b") of
          OrTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()

  describe "And" $ do
    describe "And construction" $ do
      it "And with both concrete" $ do
        andb (concTerm True) (concTerm True) `shouldBe` concTerm True
        andb (concTerm True) (concTerm False) `shouldBe` concTerm False
        andb (concTerm False) (concTerm True) `shouldBe` concTerm False
        andb (concTerm False) (concTerm False) `shouldBe` concTerm False
      it "And on general symbolic" $ do
        andb (ssymbTerm "a") (ssymbTerm "b")
          `shouldBe` constructBinary And (ssymbTerm "a" :: Term Bool) (ssymbTerm "b" :: Term Bool)
      it "And(x, y) -> False" $ do
        andb (concTerm False) (ssymbTerm "b") `shouldBe` concTerm False
        andb (ssymbTerm "a") (concTerm False) `shouldBe` concTerm False
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` concTerm False
        andb (notb (ssymbTerm "a")) (ssymbTerm "a") `shouldBe` concTerm False
        andb (ssymbTerm "a") (notb (ssymbTerm "a")) `shouldBe` concTerm False
      it "And(x, y) -> x" $ do
        andb (ssymbTerm "a") (concTerm True) `shouldBe` ssymbTerm "a"
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
        andb (ssymbTerm "a") (ssymbTerm "a") `shouldBe` ssymbTerm "a"
      it "And(x, y) -> y" $ do
        andb (concTerm True) (ssymbTerm "a") `shouldBe` ssymbTerm "a"
        andb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
      it "And(x, And(y1, y2)) -> False" $ do
        andb (notb (ssymbTerm "a")) (andb (ssymbTerm "a") (ssymbTerm "b")) `shouldBe` concTerm False
        andb (ssymbTerm "a") (andb (notb (ssymbTerm "a")) (ssymbTerm "b")) `shouldBe` concTerm False
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` concTerm False

        andb (notb (ssymbTerm "a")) (andb (ssymbTerm "b") (ssymbTerm "a")) `shouldBe` concTerm False
        andb (ssymbTerm "a") (andb (ssymbTerm "b") (notb (ssymbTerm "a"))) `shouldBe` concTerm False
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` concTerm False
      it "And(x, And(y1, y2)) -> And(x, y2)" $ do
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "And(x, And(y1, y2)) -> And(x, y1)" $ do
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "And(x, y@And(y1, y2)) -> y" $ do
        andb (ssymbTerm "a") (andb (ssymbTerm "a") (ssymbTerm "b"))
          `shouldBe` andb (ssymbTerm "a") (ssymbTerm "b")
        andb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b"))
          `shouldBe` andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
        andb (ssymbTerm "a") (andb (ssymbTerm "b") (ssymbTerm "a"))
          `shouldBe` andb (ssymbTerm "b") (ssymbTerm "a")
        andb
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)))
          `shouldBe` andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "And(And(x1, x2), y) -> False" $ do
        andb (andb (ssymbTerm "a") (ssymbTerm "b")) (notb (ssymbTerm "a")) `shouldBe` concTerm False
        andb (andb (notb (ssymbTerm "a")) (ssymbTerm "b")) (ssymbTerm "a") `shouldBe` concTerm False
        andb
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` concTerm False

        andb (andb (ssymbTerm "b") (ssymbTerm "a")) (notb (ssymbTerm "a")) `shouldBe` concTerm False
        andb (andb (ssymbTerm "b") (notb (ssymbTerm "a"))) (ssymbTerm "a") `shouldBe` concTerm False
        andb
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` concTerm False
      it "And(x@And(x1, x2), y) -> x" $ do
        andb (andb (ssymbTerm "a") (ssymbTerm "b")) (ssymbTerm "a")
          `shouldBe` andb (ssymbTerm "a") (ssymbTerm "b")
        andb
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b"))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
        andb (andb (ssymbTerm "b") (ssymbTerm "a")) (ssymbTerm "a")
          `shouldBe` andb (ssymbTerm "b") (ssymbTerm "a")
        andb
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)))
          (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
          `shouldBe` andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "And(And(x1, x2), y) -> And(x2, y)" $ do
        andb
          (andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "And(And(x1, x2), y) -> And(x1, y)" $ do
        andb
          (andb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
      it "And(x, Or(y1, y2)) -> x" $ do
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
      it "And(x, Or(y1, y2)) -> And(x, y2)" $ do
        andb (ssymbTerm "a") (orb (notb (ssymbTerm "a")) (ssymbTerm "b"))
          `shouldBe` andb (ssymbTerm "a") (ssymbTerm "b")
        andb (notb (ssymbTerm "a")) (orb (ssymbTerm "a") (ssymbTerm "b"))
          `shouldBe` andb (notb (ssymbTerm "a")) (ssymbTerm "b")
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          `shouldBe` andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "And(Or(x1, x2), y) -> y" $ do
        andb
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
        andb
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          `shouldBe` eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)
      it "And(x, Or(y1, y2)) -> And(x, y1)" $ do
        andb (ssymbTerm "a") (orb (ssymbTerm "b") (notb (ssymbTerm "a")))
          `shouldBe` andb (ssymbTerm "a") (ssymbTerm "b")
        andb (notb (ssymbTerm "a")) (orb (ssymbTerm "b") (ssymbTerm "a"))
          `shouldBe` andb (notb (ssymbTerm "a")) (ssymbTerm "b")
        andb
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          `shouldBe` andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b")
      it "And(Not(x), Not(y)) -> Not(Or(x, y))" $ do
        andb (notb (ssymbTerm "a")) (notb (ssymbTerm "b"))
          `shouldBe` notb (orb (ssymbTerm "a") (ssymbTerm "b"))
    describe "And pattern" $ do
      it "And pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          AndTerm (_ :: Term Bool) _ -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case andb (ssymbTerm "a" :: Term Bool) (ssymbTerm "b") of
          AndTerm v1 v2 -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()
  describe "ITE" $ do
    describe "ITE construction" $ do
      it "ITE with concrete condition" $ do
        iteterm (concTerm True) (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` ssymbTerm "a"
        iteterm (concTerm False) (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` ssymbTerm "b"
      it "ITE with same branches" $ do
        iteterm (ssymbTerm "c") (ssymbTerm "a" :: Term Integer) (ssymbTerm "a")
          `shouldBe` ssymbTerm "a"
      it "ITE with both not" $ do
        iteterm (ssymbTerm "c") (notb $ ssymbTerm "a") (notb $ ssymbTerm "b")
          `shouldBe` notb (iteterm (ssymbTerm "c") (ssymbTerm "a") (ssymbTerm "b"))
      it "ITE with not in condition" $ do
        iteterm (notb $ ssymbTerm "c") (ssymbTerm "a" :: Term Integer) (ssymbTerm "b")
          `shouldBe` iteterm (ssymbTerm "c") (ssymbTerm "b") (ssymbTerm "a")
      it "ITE with all arguments as ITE with same conditions" $ do
        iteterm
          (iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "c"))
          (iteterm (ssymbTerm "a") (ssymbTerm "d" :: Term Integer) (ssymbTerm "e"))
          (iteterm (ssymbTerm "a") (ssymbTerm "f" :: Term Integer) (ssymbTerm "g"))
          `shouldBe` iteterm
            (ssymbTerm "a")
            (iteterm (ssymbTerm "b") (ssymbTerm "d") (ssymbTerm "f"))
            (iteterm (ssymbTerm "c") (ssymbTerm "e") (ssymbTerm "g"))
      it "ITE with true branch as ITE" $ do
        iteterm
          (ssymbTerm "a")
          (iteterm (ssymbTerm "a") (ssymbTerm "b" :: Term Integer) (ssymbTerm "c"))
          (ssymbTerm "d")
          `shouldBe` iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "d")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          ( iteterm
              (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))
              (ssymbTerm "b" :: Term Integer)
              (ssymbTerm "c")
          )
          (ssymbTerm "d")
          `shouldBe` iteterm
            (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
            (ssymbTerm "c")
            (ssymbTerm "d")
        iteterm
          (ssymbTerm "a")
          (iteterm (ssymbTerm "b") (ssymbTerm "c" :: Term Integer) (ssymbTerm "d"))
          (ssymbTerm "c")
          `shouldBe` iteterm
            (orb (notb $ ssymbTerm "a") (ssymbTerm "b"))
            (ssymbTerm "c")
            (ssymbTerm "d")
        iteterm
          (ssymbTerm "a")
          (iteterm (ssymbTerm "b") (ssymbTerm "c" :: Term Integer) (ssymbTerm "d"))
          (ssymbTerm "d")
          `shouldBe` iteterm
            (andb (ssymbTerm "a") (ssymbTerm "b"))
            (ssymbTerm "c")
            (ssymbTerm "d")
      it "ITE with false branch as ITE" $ do
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (iteterm (ssymbTerm "a") (ssymbTerm "c" :: Term Integer) (ssymbTerm "d"))
          `shouldBe` iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "d")
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (iteterm (ssymbTerm "c") (ssymbTerm "b" :: Term Integer) (ssymbTerm "d"))
          `shouldBe` iteterm
            (orb (ssymbTerm "a") (ssymbTerm "c"))
            (ssymbTerm "b")
            (ssymbTerm "d")
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (iteterm (ssymbTerm "c") (ssymbTerm "d" :: Term Integer) (ssymbTerm "b"))
          `shouldBe` iteterm
            (orb (ssymbTerm "a") (notb $ ssymbTerm "c"))
            (ssymbTerm "b")
            (ssymbTerm "d")
      it "ITE with both And" $ do
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "b") (ssymbTerm "c"))
          (andb (ssymbTerm "b") (ssymbTerm "d"))
          `shouldBe` andb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "c") (ssymbTerm "b"))
          (andb (ssymbTerm "b") (ssymbTerm "d"))
          `shouldBe` andb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "b") (ssymbTerm "c"))
          (andb (ssymbTerm "d") (ssymbTerm "b"))
          `shouldBe` andb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "c") (ssymbTerm "b"))
          (andb (ssymbTerm "d") (ssymbTerm "b"))
          `shouldBe` andb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
      it "ITE with left And" $ do
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "b") (ssymbTerm "c"))
          (ssymbTerm "b")
          `shouldBe` andb (ssymbTerm "b") (orb (notb (ssymbTerm "a")) (ssymbTerm "c"))
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "b") (ssymbTerm "c"))
          (ssymbTerm "c")
          `shouldBe` andb (ssymbTerm "c") (orb (notb (ssymbTerm "a")) (ssymbTerm "b"))
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (andb (notb $ ssymbTerm "a") (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` andb (notb $ ssymbTerm "a") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (ssymbTerm "c")
          `shouldBe` andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "b") (notb $ ssymbTerm "a"))
          (ssymbTerm "c")
          `shouldBe` andb (notb $ ssymbTerm "a") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` iteterm (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "a") (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (andb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (ssymbTerm "c")
          `shouldBe` iteterm (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (andb (ssymbTerm "b") (ssymbTerm "a"))
          (ssymbTerm "c")
          `shouldBe` iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "c")
      it "ITE with right And" $ do
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (andb (ssymbTerm "b") (ssymbTerm "c"))
          `shouldBe` andb (ssymbTerm "b") (orb (ssymbTerm "a") (ssymbTerm "c"))
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "c")
          (andb (ssymbTerm "b") (ssymbTerm "c"))
          `shouldBe` andb (ssymbTerm "c") (orb (ssymbTerm "a") (ssymbTerm "b"))

      it "ITE with both Or" $ do
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "b") (ssymbTerm "c"))
          (orb (ssymbTerm "b") (ssymbTerm "d"))
          `shouldBe` orb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "c") (ssymbTerm "b"))
          (orb (ssymbTerm "b") (ssymbTerm "d"))
          `shouldBe` orb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "b") (ssymbTerm "c"))
          (orb (ssymbTerm "d") (ssymbTerm "b"))
          `shouldBe` orb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "c") (ssymbTerm "b"))
          (orb (ssymbTerm "d") (ssymbTerm "b"))
          `shouldBe` orb (ssymbTerm "b") (iteterm (ssymbTerm "a") (ssymbTerm "c") (ssymbTerm "d"))
      it "ITE with left Or" $ do
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "b") (ssymbTerm "c"))
          (ssymbTerm "b")
          `shouldBe` orb (ssymbTerm "b") (andb (ssymbTerm "a") (ssymbTerm "c"))
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "b") (ssymbTerm "c"))
          (ssymbTerm "c")
          `shouldBe` orb (ssymbTerm "c") (andb (ssymbTerm "a") (ssymbTerm "b"))
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` iteterm (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (orb (notb $ ssymbTerm "a") (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (ssymbTerm "c")
          `shouldBe` iteterm (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "b") (notb $ ssymbTerm "a"))
          (ssymbTerm "c")
          `shouldBe` iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "a") (ssymbTerm "b"))
          (ssymbTerm "c")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (orb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)))
          (ssymbTerm "c")
          `shouldBe` orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (orb (ssymbTerm "b") (ssymbTerm "a"))
          (ssymbTerm "c")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "c")
      it "ITE with right Or" $ do
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (orb (ssymbTerm "b") (ssymbTerm "c"))
          `shouldBe` orb (ssymbTerm "b") (andb (notb (ssymbTerm "a")) (ssymbTerm "c"))
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "c")
          (orb (ssymbTerm "b") (ssymbTerm "c"))
          `shouldBe` orb (ssymbTerm "c") (andb (notb (ssymbTerm "a")) (ssymbTerm "b"))
      it "ITE with const boolean in branches" $ do
        iteterm
          (ssymbTerm "a")
          (concTerm True)
          (ssymbTerm "b")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "b")
        iteterm
          (ssymbTerm "a")
          (concTerm False)
          (ssymbTerm "b")
          `shouldBe` andb (notb $ ssymbTerm "a") (ssymbTerm "b")
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (concTerm True)
          `shouldBe` orb (notb $ ssymbTerm "a") (ssymbTerm "b")
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (concTerm False)
          `shouldBe` andb (ssymbTerm "a") (ssymbTerm "b")
      it "ITE with condition equal to some branch" $ do
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "a")
          (ssymbTerm "b")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "b")
        iteterm
          (ssymbTerm "a")
          (ssymbTerm "b")
          (ssymbTerm "a")
          `shouldBe` andb (ssymbTerm "a") (ssymbTerm "b")
      it "ITE with left Not" $ do
        iteterm (ssymbTerm "a") (notb (ssymbTerm "a")) (ssymbTerm "b")
          `shouldBe` andb (notb $ ssymbTerm "a") (ssymbTerm "b")
      it "ITE with right Not" $ do
        iteterm (ssymbTerm "a") (ssymbTerm "b") (notb (ssymbTerm "a"))
          `shouldBe` orb (notb $ ssymbTerm "a") (ssymbTerm "b")
      it "ITE with left Not And" $ do
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (notb (andb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b")))
          (ssymbTerm "c")
          `shouldBe` orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (notb (andb (notb $ ssymbTerm "a") (ssymbTerm "b")))
          (ssymbTerm "c")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (notb (andb (ssymbTerm "b") (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 2))))
          (ssymbTerm "c")
          `shouldBe` orb (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (notb (andb (ssymbTerm "b") (notb $ ssymbTerm "a")))
          (ssymbTerm "c")
          `shouldBe` orb (ssymbTerm "a") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (notb (andb (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2)) (ssymbTerm "b")))
          (ssymbTerm "c")
          `shouldBe` iteterm (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (notb $ ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (notb (andb (ssymbTerm "a") (ssymbTerm "b")))
          (ssymbTerm "c")
          `shouldBe` iteterm (ssymbTerm "a") (notb $ ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1))
          (notb (andb (ssymbTerm "b") (neterm (ssymbTerm "a" :: Term Integer) (concTerm 2))))
          (ssymbTerm "c")
          `shouldBe` iteterm (eqterm (ssymbTerm "a" :: Term Integer) (concTerm 1)) (notb $ ssymbTerm "b") (ssymbTerm "c")
        iteterm
          (ssymbTerm "a")
          (notb (andb (ssymbTerm "b") (ssymbTerm "a")))
          (ssymbTerm "c")
          `shouldBe` iteterm (ssymbTerm "a") (notb $ ssymbTerm "b") (ssymbTerm "c")
  describe "Imply" $ do
    it "implyb should work" $ do
      ssymbTerm "a" `implyb` ssymbTerm "b"
        `shouldBe` orb (notb $ ssymbTerm "a") (ssymbTerm "b")
  describe "Xor" $ do
    it "xorb should work" $ do
      ssymbTerm "a" `xorb` ssymbTerm "b"
        `shouldBe` orb
          (andb (notb $ ssymbTerm "a") (ssymbTerm "b"))
          (andb (ssymbTerm "a") (notb $ ssymbTerm "b"))
