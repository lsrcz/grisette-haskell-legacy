{-# LANGUAGE BinaryLiterals #-}

module Grisette.Data.SMT.CEGISSpec where

import Control.Monad.Except
import qualified Data.HashSet as S
import Data.Proxy
import qualified Data.SBV as SBV
import Grisette.Control.Exception
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.BitVector
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SymEval
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.SymPrim
import Test.Hspec

testCegis :: (HasCallStack, ExtractSymbolics (S.HashSet TermSymbol) a) => GrisetteSMTConfig i -> Bool -> a -> [SymBool] -> Expectation
testCegis config shouldSuccess a bs = do
  x <- cegisWithTranslation DefaultVerificationCondition config (a, ssymb "internal" :: SymInteger) (buildFormula bs)
  case x of
    Left _ -> shouldSuccess `shouldBe` False
    Right m -> do
      shouldSuccess `shouldBe` True
      verify bs
      where
        verify [] = return ()
        verify (v : vs) = do
          y <- solveWith config (symeval False m $ nots v)
          case y of
            Left _ -> do
              verify vs
            Right _ -> expectationFailure $ "Failed to verify " ++ show v ++ " with the model " ++ show m
  where
    buildFormula :: [SymBool] -> ExceptT VerificationConditions UnionM ()
    buildFormula l = do
      gassertWithError AssumptionViolation ((ssymb "internal" :: SymInteger) >=~ 0)
      go l 0
      where
        go :: [SymBool] -> SymInteger -> ExceptT VerificationConditions UnionM ()
        go [] _ = return ()
        go (x : xs) i =
          mrgIf
            (ssymb "internal" >=~ i &&~ ssymb "internal" <~ (i + 1))
            (gassertWithError AssertionViolation x)
            (go xs (i + 1))

spec :: Spec
spec = do
  let unboundedConfig = UnboundedReasoning SBV.z3 --{SBV.verbose=True}
  describe "Boolean" $ do
    describe "Basic" $ do
      it "testCegis should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [ssymb "a", ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          False
          ()
          [ssymb "a", nots $ ssymb "a"]
    describe "And" $ do
      it "And should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [ssymb "a" &&~ ssymb "b", ssymb "b" &&~ nots (ssymb "c"), ssymb "a", ssymb "b", nots (ssymb "c")]
        testCegis
          unboundedConfig
          False
          ()
          [ssymb "a" &&~ ssymb "b", ssymb "b" &&~ nots (ssymb "c"), ssymb "a", ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          True
          (ssymb "a" :: SymBool)
          [nots $ ssymb "a" &&~ ssymb "b", nots $ ssymb "b"]
        testCegis
          unboundedConfig
          False
          (ssymb "a" :: SymBool)
          [nots $ ssymb "a" &&~ ssymb "b", ssymb "b"]
    describe "Or" $ do
      it "Or should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [ssymb "a" ||~ ssymb "b", ssymb "b" ||~ nots (ssymb "c"), ssymb "a", ssymb "b", nots (ssymb "c")]
        testCegis
          unboundedConfig
          True
          ()
          [ssymb "a" ||~ ssymb "b", ssymb "b" ||~ nots (ssymb "c"), ssymb "a", ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          True
          (ssymb "a" :: SymBool)
          [ssymb "a" ||~ ssymb "b", ssymb "b"]
        testCegis
          unboundedConfig
          False
          (ssymb "a" :: SymBool)
          [ssymb "a" ||~ ssymb "b", nots $ ssymb "b"]
    describe "And / Or" $ do
      it "And / Or should be consistent" $ do
        testCegis
          unboundedConfig
          True
          ()
          [ssymb "a" &&~ ssymb "b", ssymb "a" ||~ ssymb "b"]
        testCegis
          unboundedConfig
          True
          ()
          [nots $ ssymb "a" &&~ ssymb "b", ssymb "a" ||~ ssymb "b"]
        testCegis
          unboundedConfig
          False
          ()
          [ssymb "a" &&~ ssymb "b", nots $ ssymb "a" ||~ ssymb "b"]
        testCegis
          unboundedConfig
          True
          ()
          [nots $ ssymb "a" &&~ ssymb "b", nots $ ssymb "a" ||~ ssymb "b"]
    describe "Eqv" $ do
      it "Eqv should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [(ssymb "a" :: SymBool) ==~ ssymb "b", ssymb "a", ssymb "b"]
        testCegis
          unboundedConfig
          True
          ()
          [(ssymb "a" :: SymBool) ==~ ssymb "b", nots $ ssymb "a", nots $ ssymb "b"]
        testCegis
          unboundedConfig
          False
          ()
          [(ssymb "a" :: SymBool) ==~ ssymb "b", nots $ ssymb "a", ssymb "b"]
        testCegis
          unboundedConfig
          False
          ()
          [(ssymb "a" :: SymBool) ==~ ssymb "b", nots $ ssymb "a", ssymb "b"]
        testCegis
          unboundedConfig
          True
          ()
          [(ssymb "a" :: SymBool) ==~ ssymb "b", nots (ssymb "a") `xors` ssymb "b"]
        testCegis
          unboundedConfig
          False
          ()
          [(ssymb "a" :: SymBool) ==~ ssymb "b", ssymb "a" `xors` ssymb "b"]
      it "ites should work" $ do
        testCegis
          unboundedConfig
          True
          (ssymb "c" :: SymBool)
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), ssymb "a", ssymb "b"]
        testCegis
          unboundedConfig
          False
          (ssymb "c" :: SymBool)
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), nots $ ssymb "a"]
        testCegis
          unboundedConfig
          True
          (ssymb "b" :: SymBool)
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), nots $ ssymb "a", ssymb "c"]
        testCegis
          unboundedConfig
          False
          (ssymb "b" :: SymBool)
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), ssymb "a"]
        testCegis
          unboundedConfig
          True
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), ssymb "a", ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          True
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), ssymb "a", ssymb "b", nots $ ssymb "c"]
        testCegis
          unboundedConfig
          True
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), nots $ ssymb "a", ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          True
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), nots $ ssymb "a", nots $ ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          False
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), ssymb "a", nots $ ssymb "b", ssymb "c"]
        testCegis
          unboundedConfig
          False
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), ssymb "a", nots $ ssymb "b", nots $ ssymb "c"]
        testCegis
          unboundedConfig
          False
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), nots $ ssymb "a", ssymb "b", nots $ ssymb "c"]
        testCegis
          unboundedConfig
          False
          ()
          [ites (ssymb "a" :: SymBool) (ssymb "b") (ssymb "c"), nots $ ssymb "a", nots $ ssymb "b", nots $ ssymb "c"]
  describe "Different sized BV" $ do
    let a = ssymb "a" :: SymSignedBV 5
    let b = ssymb "b" :: SymSignedBV 5
    let c = ssymb "c" :: SymSignedBV 5
    let d = ssymb "c" :: SymSignedBV 10
    describe "Extract" $ do
      it "Extract should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [bvextract (Proxy @2) (Proxy @2) a ==~ conc 1, a ==~ conc 0b10101]
        testCegis
          unboundedConfig
          False
          ()
          [bvextract (Proxy @2) (Proxy @2) a ==~ conc 1, a ==~ conc 0b10001]
      it "Extract should work when lowered twice" $ do
        testCegis
          unboundedConfig
          True
          a
          [bvextract (Proxy @2) (Proxy @2) (bvconcat a b) ==~ conc 1]
        testCegis
          unboundedConfig
          True
          b
          [bvextract (Proxy @7) (Proxy @2) (bvconcat a b) ==~ conc 1]
    describe "Concat" $ do
      it "Concat should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [bvconcat a b ==~ d, a ==~ conc 1, b ==~ conc 1, d ==~ conc 0b100001]
        testCegis
          unboundedConfig
          False
          ()
          [bvconcat a b ==~ d, a ==~ conc 1, b ==~ conc 1, d ==~ conc 0b100010]
      it "Concat should work when lowered twice" $ do
        testCegis
          unboundedConfig
          True
          (a, c)
          [bvconcat c (bvextract (Proxy @2) (Proxy @2) (bvconcat a b)) ==~ bvconcat c (conc 1 :: SymSignedBV 2)]
        testCegis
          unboundedConfig
          True
          (b, c)
          [bvconcat c (bvextract (Proxy @7) (Proxy @2) (bvconcat a b)) ==~ bvconcat c (conc 1 :: SymSignedBV 2)]
    describe "Zext" $ do
      it "bvzeroExtend should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [bvzeroExtend a ==~ d, a ==~ conc 1, d ==~ (conc 1 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          True
          ()
          [bvzeroExtend a ==~ d, a ==~ conc 0b11111, d ==~ (conc 0b11111 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          False
          ()
          [bvzeroExtend a ==~ d, d ==~ (conc 0b111111 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          False
          ()
          [bvzeroExtend a ==~ d, d ==~ (conc 0b1111111111 :: SymSignedBV 10)]
      it "bvzeroExtend should work when lowered twice" $ do
        testCegis
          unboundedConfig
          True
          a
          [bvzeroExtend (bvextract (Proxy @2) (Proxy @2) (bvconcat a b)) ==~ (conc 1 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          True
          b
          [bvzeroExtend (bvextract (Proxy @7) (Proxy @2) (bvconcat a b)) ==~ (conc 1 :: SymSignedBV 10)]
    describe "Sext" $ do
      it "bvsignExtend should work" $ do
        testCegis
          unboundedConfig
          True
          ()
          [bvsignExtend a ==~ d, a ==~ conc 1, d ==~ (conc 1 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          True
          ()
          [bvsignExtend a ==~ d, a ==~ conc 0b11111, d ==~ (conc 0b1111111111 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          False
          ()
          [bvsignExtend a ==~ d, d ==~ (conc 0b111111 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          False
          ()
          [bvsignExtend a ==~ d, d ==~ (conc 0b11111 :: SymSignedBV 10)]
      it "bvsignExtend should work when lowered twice" $ do
        testCegis
          unboundedConfig
          True
          a
          [bvsignExtend (bvextract (Proxy @2) (Proxy @2) (bvconcat a b)) ==~ (conc 1 :: SymSignedBV 10)]
        testCegis
          unboundedConfig
          True
          b
          [bvsignExtend (bvextract (Proxy @7) (Proxy @2) (bvconcat a b)) ==~ (conc 1 :: SymSignedBV 10)]
