{-# LANGUAGE OverloadedStrings #-}

module Grisette.Data.SMT.SExprSpec where

-- import ByteString.StrictBuilder
import Grisette.Data.SMT.SExpr as SExpr
import Test.Hspec

spec :: Spec
spec = do
  describe "SExpr show correct" $ do
    it "Symbol correct" $ do
      sexprByteString (SExpr.symbol "a") `shouldBe` "a"
    it "Bool lit correct" $ do
      sexprByteString (trueLit) `shouldBe` "true"
      sexprByteString (falseLit) `shouldBe` "false"
      sexprByteString (boolLit True) `shouldBe` "true"
      sexprByteString (boolLit False) `shouldBe` "false"
    it "Bool ops correct" $ do
      sexprByteString (SExpr.not (SExpr.symbol "a")) `shouldBe` "(not a)"
      sexprByteString (SExpr.and (SExpr.symbol "a") (SExpr.symbol "b")) `shouldBe` "(and a b)"
      sexprByteString (SExpr.or (SExpr.symbol "a") (SExpr.symbol "b")) `shouldBe` "(or a b)"
      sexprByteString (SExpr.andMany [SExpr.symbol "a", SExpr.symbol "b", SExpr.symbol "c"])
        `shouldBe` "(and a b c)"
      sexprByteString (SExpr.orMany [SExpr.symbol "a", SExpr.symbol "b", SExpr.symbol "c"])
        `shouldBe` "(or a b c)"
    it "sort correct" $ do
      sexprByteString SExpr.intSort `shouldBe` "Int"
      sexprByteString SExpr.boolSort `shouldBe` "Bool"
    it "set-logic correct" $ do
      sexprByteString (SExpr.setLogic QF_BV) `shouldBe` "(set-logic QF_BV)"
      sexprByteString (SExpr.setLogic ALL) `shouldBe` "(set-logic ALL)"
    it "define-fun correct" $ do
      sexprByteString (SExpr.defineFun "x" [] boolSort $ SExpr.symbol "b")
        `shouldBe` "(define-fun x () Bool b)"
      sexprByteString (SExpr.defineFun "y" [("b", boolSort)] boolSort $ SExpr.not $ SExpr.symbol "b")
        `shouldBe` "(define-fun y ((b Bool)) Bool (not b))"
    it "check-sat correct" $ do
      sexprByteString checkSat `shouldBe` "(check-sat)"
    it "get-model correct" $ do
      sexprByteString getModel `shouldBe` "(get-model)"
