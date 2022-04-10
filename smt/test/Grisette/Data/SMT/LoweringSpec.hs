{-# LANGUAGE AllowAmbiguousTypes #-}

module Grisette.Data.SMT.LoweringSpec where

import Control.Monad.Trans
import Data.BitVector.Sized.Signed
import Data.Dynamic
import qualified Data.HashMap.Strict as M
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Num
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Lowering
import Test.Hspec
import Grisette.Data.Prim.BV
import Data.Proxy
import Data.BitVector.Sized.Unsigned
import Grisette.Data.Prim.Bits
import Data.Bits

testUnaryOpLowering' ::
  forall a b as n tag.
  ( HasCallStack,
    UnaryOp tag a b,
    SBV.EqSymbolic (TermTy n b),
    Typeable (TermTy n a),
    SBV.SymVal as,
    TermTy n a ~ SBV.SBV as,
    Show as
  ) =>
  GrisetteSMTConfig n ->
  tag ->
  (TermTy n a -> TermTy n b) ->
  Expectation
testUnaryOpLowering' config t sbvfun = do
  let a :: Term a = ssymbTerm "a"
  let fa :: Term b = constructUnary t a
  SBV.runSMTWith (sbvConfig config) $ do
    (m, lt) <- lowerSinglePrim config fa
    let sbva :: Maybe (TermTy n a) = M.lookup (SomeTerm a) (biMapToSBV m) >>= fromDynamic
    case sbva of
      Nothing -> lift $ expectationFailure "Failed to extract the term"
      Just sbvav -> SBV.query $ do
        SBV.constrain $ lt SBV..== sbvfun sbvav
        satres <- SBV.checkSat
        case satres of
          SBV.Sat -> return ()
          _ -> lift $ expectationFailure $ "Lowering for " ++ show t ++ " generated unsolvable formula"
  SBV.runSMTWith (sbvConfig config) $ do
    (m, lt) <- lowerSinglePrim config fa
    let sbvv :: Maybe (TermTy n a) = M.lookup (SomeTerm a) (biMapToSBV m) >>= fromDynamic
    case sbvv of
      Nothing -> lift $ expectationFailure "Failed to extract the term"
      Just sbvvv -> SBV.query $ do
        SBV.constrain $ lt SBV../= sbvfun sbvvv
        r <- SBV.checkSat
        case r of
          SBV.Sat -> do
            counterExample <- SBV.getValue sbvvv
            lift $ expectationFailure $ "Translation counter example found: " ++ show counterExample
          SBV.Unsat -> return ()
          _ -> lift $ expectationFailure $ "Lowering for " ++ show t ++ " generated unknown formula"

testBinaryOpLowering' ::
  forall a b c as bs n tag.
  ( HasCallStack,
    BinaryOp tag a b c,
    SBV.EqSymbolic (TermTy n c),
    Typeable (TermTy n a),
    Typeable (TermTy n b),
    SBV.SymVal as,
    SBV.SymVal bs,
    Show as,
    Show bs,
    TermTy n a ~ SBV.SBV as,
    TermTy n b ~ SBV.SBV bs
  ) =>
  GrisetteSMTConfig n ->
  tag ->
  (TermTy n a -> TermTy n b -> TermTy n c) ->
  Expectation
testBinaryOpLowering' config t sbvfun = do
  let a :: Term a = ssymbTerm "a"
  let b :: Term b = ssymbTerm "b"
  let fab :: Term c = constructBinary t a b
  SBV.runSMTWith (sbvConfig config) $ do
    (m, lt) <- lowerSinglePrim config fab
    let sbva :: Maybe (TermTy n a) = M.lookup (SomeTerm a) (biMapToSBV m) >>= fromDynamic
    let sbvb :: Maybe (TermTy n b) = M.lookup (SomeTerm b) (biMapToSBV m) >>= fromDynamic
    case (sbva, sbvb) of
      (Just sbvav, Just sbvbv) -> SBV.query $ do
        SBV.constrain $ lt SBV..== sbvfun sbvav sbvbv
        satres <- SBV.checkSat
        case satres of
          SBV.Sat -> return ()
          _ -> lift $ expectationFailure $ "Lowering for " ++ show t ++ " generated unsolvable formula"
      _ -> lift $ expectationFailure "Failed to extract the term"
  SBV.runSMTWith (sbvConfig config) $ do
    (m, lt) <- lowerSinglePrim config fab
    let sbva :: Maybe (TermTy n a) = M.lookup (SomeTerm a) (biMapToSBV m) >>= fromDynamic
    let sbvb :: Maybe (TermTy n b) = M.lookup (SomeTerm b) (biMapToSBV m) >>= fromDynamic
    case (sbva, sbvb) of
      (Just sbvav, Just sbvbv) -> SBV.query $ do
        SBV.constrain $ lt SBV../= sbvfun sbvav sbvbv
        r <- SBV.checkSat
        case r of
          SBV.Sat -> do
            counterExampleA <- SBV.getValue sbvav
            counterExampleB <- SBV.getValue sbvbv
            lift $ expectationFailure $ "Translation counter example found: " ++ show (counterExampleA, counterExampleB)
          SBV.Unsat -> return ()
          _ -> lift $ expectationFailure $ "Lowering for " ++ show t ++ " generated unknown formula"
      _ -> lift $ expectationFailure "Failed to extract the term"

testTernaryOpLowering' ::
  forall a b c d as bs cs n tag.
  ( HasCallStack,
    TernaryOp tag a b c d,
    SBV.EqSymbolic (TermTy n d),
    Typeable (TermTy n a),
    Typeable (TermTy n b),
    Typeable (TermTy n c),
    SBV.SymVal as,
    SBV.SymVal bs,
    SBV.SymVal cs,
    Show as,
    Show bs,
    Show cs,
    TermTy n a ~ SBV.SBV as,
    TermTy n b ~ SBV.SBV bs,
    TermTy n c ~ SBV.SBV cs
  ) =>
  GrisetteSMTConfig n ->
  tag ->
  (TermTy n a -> TermTy n b -> TermTy n c -> TermTy n d) ->
  Expectation
testTernaryOpLowering' config t sbvfun = do
  let a :: Term a = ssymbTerm "a"
  let b :: Term b = ssymbTerm "b"
  let c :: Term c = ssymbTerm "c"
  let fabc :: Term d = constructTernary t a b c
  SBV.runSMTWith (sbvConfig config) $ do
    (m, lt) <- lowerSinglePrim config fabc
    let sbva :: Maybe (TermTy n a) = M.lookup (SomeTerm a) (biMapToSBV m) >>= fromDynamic
    let sbvb :: Maybe (TermTy n b) = M.lookup (SomeTerm b) (biMapToSBV m) >>= fromDynamic
    let sbvc :: Maybe (TermTy n c) = M.lookup (SomeTerm c) (biMapToSBV m) >>= fromDynamic
    case (sbva, sbvb, sbvc) of
      (Just sbvav, Just sbvbv, Just sbvcv) -> SBV.query $ do
        SBV.constrain $ lt SBV..== sbvfun sbvav sbvbv sbvcv
        satres <- SBV.checkSat
        case satres of
          SBV.Sat -> return ()
          _ -> lift $ expectationFailure $ "Lowering for " ++ show t ++ " generated unsolvable formula"
      _ -> lift $ expectationFailure "Failed to extract the term"
  SBV.runSMTWith (sbvConfig config) $ do
    (m, lt) <- lowerSinglePrim config fabc
    let sbva :: Maybe (TermTy n a) = M.lookup (SomeTerm a) (biMapToSBV m) >>= fromDynamic
    let sbvb :: Maybe (TermTy n b) = M.lookup (SomeTerm b) (biMapToSBV m) >>= fromDynamic
    let sbvc :: Maybe (TermTy n c) = M.lookup (SomeTerm c) (biMapToSBV m) >>= fromDynamic
    case (sbva, sbvb, sbvc) of
      (Just sbvav, Just sbvbv, Just sbvcv) -> SBV.query $ do
        SBV.constrain $ lt SBV../= sbvfun sbvav sbvbv sbvcv
        r <- SBV.checkSat
        case r of
          SBV.Sat -> do
            counterExampleA <- SBV.getValue sbvav
            counterExampleB <- SBV.getValue sbvbv
            counterExampleC <- SBV.getValue sbvcv
            lift $
              expectationFailure $
                "Translation counter example found: "
                  ++ show (counterExampleA, counterExampleB, counterExampleC)
          SBV.Unsat -> return ()
          _ -> lift $ expectationFailure $ "Lowering for " ++ show t ++ " generated unknown formula"
      _ -> lift $ expectationFailure "Failed to extract the term"

spec :: Spec
spec = do
  let unboundedConfig = UnboundedReasoning SBV.z3
  let boundedConfig = BoundedReasoning @5 SBV.z3
  describe "Test Bool Lowering" $ do
    it "Not lowering should work" $ do
      testUnaryOpLowering' @Bool @Bool unboundedConfig Not SBV.sNot
    it "And lowering should work" $ do
      testBinaryOpLowering' @Bool @Bool @Bool unboundedConfig And (SBV..&&)
      testBinaryOpLowering' @Bool @Bool @Bool
        unboundedConfig
        And
        (\x y -> SBV.sNot (x SBV..<+> y) SBV..&& (x SBV..|| y))
    it "Or lowering should work" $ do
      testBinaryOpLowering' @Bool @Bool @Bool unboundedConfig Or (SBV..||)
      testBinaryOpLowering' @Bool @Bool @Bool
        unboundedConfig
        Or
        (\x y -> (x SBV..<+> y) SBV..|| (x SBV..&& y))
    it "Eqv lowering should work" $ do
      testBinaryOpLowering' @Bool @Bool @Bool unboundedConfig Eqv (SBV..==)
      testBinaryOpLowering' @Bool @Bool @Bool
        unboundedConfig
        Eqv
        (\x y -> SBV.sNot (x SBV..<+> y))
    it "ITE lowering should work" $ do
      testTernaryOpLowering' @Bool @Bool @Bool @Bool unboundedConfig ITE SBV.ite
      testTernaryOpLowering' @Bool @Bool @Bool @Bool
        unboundedConfig
        ITE
        (\c x y -> (c SBV..=> x) SBV..&& (SBV.sNot c SBV..=> y))
  describe "Test Integer Lowering" $ do
    it "Add lowering should work" $ do
      testBinaryOpLowering' @Integer @Integer @Integer unboundedConfig (AddNum @Integer) (+)
      testBinaryOpLowering' @Integer @Integer @Integer
        unboundedConfig
        (AddNum @Integer)
        (\x y -> (x + 1) * (y + 1) - x * y - 1)
      testBinaryOpLowering' @Integer @Integer @Integer boundedConfig (AddNum @Integer) (+)
      testBinaryOpLowering' @Integer @Integer @Integer
        boundedConfig
        (AddNum @Integer)
        (\x y -> (x + 1) * (y + 1) - x * y - 1)
    it "Uminus lowering should work" $ do
      testUnaryOpLowering' @Integer @Integer unboundedConfig UMinusNum negate
      testUnaryOpLowering' @Integer @Integer
        unboundedConfig
        UMinusNum
        (\x -> (x + 1) * (x + 1) - 3 * x - x * x - 1)
      testUnaryOpLowering' @Integer @Integer boundedConfig UMinusNum negate
      testUnaryOpLowering' @Integer @Integer
        boundedConfig
        UMinusNum
        (\x -> (x + 1) * (x + 1) - 3 * x - x * x - 1)
    it "Abs lowering should work" $ do
      testUnaryOpLowering' @Integer @Integer unboundedConfig AbsNum abs
      testUnaryOpLowering' @Integer @Integer boundedConfig AbsNum abs
    it "Signum lowering should work" $ do
      testUnaryOpLowering' @Integer @Integer unboundedConfig SignumNum signum
      testUnaryOpLowering' @Integer @Integer boundedConfig SignumNum signum
    it "Times lowering should work" $ do
      testBinaryOpLowering' @Integer @Integer @Integer unboundedConfig TimesNum (*)
      testBinaryOpLowering' @Integer @Integer @Integer
        unboundedConfig
        TimesNum
        (\x y -> (x + 1) * (y + 1) - x - y - 1)
      testBinaryOpLowering' @Integer @Integer @Integer boundedConfig TimesNum (*)
      testBinaryOpLowering' @Integer @Integer @Integer
        boundedConfig
        TimesNum
        (\x y -> (x + 1) * (y + 1) - x - y - 1)
    it "Lt lowering should work" $ do
      testBinaryOpLowering' @Integer @Integer @Bool unboundedConfig LTNum (SBV..<)
      testBinaryOpLowering' @Integer @Integer @Bool
        unboundedConfig
        LTNum
        (\x y -> x * 2 - x SBV..< y * 2 - y)
      testBinaryOpLowering' @Integer @Integer @Bool boundedConfig LTNum (SBV..<)
      testBinaryOpLowering' @Integer @Integer @Bool
        boundedConfig
        LTNum
        (\x y -> x * 2 - x SBV..< y * 2 - y)
    it "Le lowering should work" $ do
      testBinaryOpLowering' @Integer @Integer @Bool unboundedConfig LENum (SBV..<=)
      testBinaryOpLowering' @Integer @Integer @Bool
        unboundedConfig
        LENum
        (\x y -> x * 2 - x SBV..<= y * 2 - y)
      testBinaryOpLowering' @Integer @Integer @Bool boundedConfig LENum (SBV..<=)
      testBinaryOpLowering' @Integer @Integer @Bool
        boundedConfig
        LENum
        (\x y -> x * 2 - x SBV..<= y * 2 - y)
    it "DivI lowering should work" $ do
      testBinaryOpLowering' @Integer @Integer @Integer unboundedConfig DivI SBV.sDiv
      testBinaryOpLowering' @Integer @Integer @Integer boundedConfig DivI SBV.sDiv
    it "ModI lowering should work" $ do
      testBinaryOpLowering' @Integer @Integer @Integer unboundedConfig ModI SBV.sMod
      testBinaryOpLowering' @Integer @Integer @Integer boundedConfig ModI SBV.sMod
  describe "Test SignedBV Lowering" $ do
    it "Add lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig (AddNum @(SignedBV 5)) (+)
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5)
        unboundedConfig
        (AddNum @(SignedBV 5))
        (\x y -> (x + 1) * (y + 1) - x * y - 1)
    it "Uminus lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig UMinusNum negate
      testUnaryOpLowering' @(SignedBV 5)
        unboundedConfig
        UMinusNum
        (\x -> (x + 1) * (x + 1) - 3 * x - x * x - 1)
    it "Abs lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig AbsNum abs
    it "Signum lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig SignumNum signum
    it "Times lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig TimesNum (*)
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5)
        unboundedConfig
        TimesNum
        (\x y -> (x + 1) * (y + 1) - x - y - 1)
    it "Lt lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig LTNum (SBV..<)
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5)
        unboundedConfig
        LTNum
        (\x y -> x * 2 - x SBV..< y * 2 - y)
    it "Le lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig LENum (SBV..<=)
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5)
        unboundedConfig
        LENum
        (\x y -> x * 2 - x SBV..<= y * 2 - y)
    it "Extract lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 1) unboundedConfig (BVTSelect @0 @1 @5 Proxy)
        (SBV.bvExtract @0 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 1) unboundedConfig (BVTSelect @1 @1 @5 Proxy)
        (SBV.bvExtract @1 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 1) unboundedConfig (BVTSelect @2 @1 @5 Proxy)
        (SBV.bvExtract @2 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 1) unboundedConfig (BVTSelect @3 @1 @5 Proxy)
        (SBV.bvExtract @3 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 1) unboundedConfig (BVTSelect @4 @1 @5 Proxy)
        (SBV.bvExtract @4 @4 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 2) unboundedConfig (BVTSelect @0 @2 @5 Proxy)
        (SBV.bvExtract @1 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 2) unboundedConfig (BVTSelect @1 @2 @5 Proxy)
        (SBV.bvExtract @2 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 2) unboundedConfig (BVTSelect @2 @2 @5 Proxy)
        (SBV.bvExtract @3 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 2) unboundedConfig (BVTSelect @3 @2 @5 Proxy)
        (SBV.bvExtract @4 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 3) unboundedConfig (BVTSelect @0 @3 @5 Proxy)
        (SBV.bvExtract @2 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 3) unboundedConfig (BVTSelect @1 @3 @5 Proxy)
        (SBV.bvExtract @3 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 3) unboundedConfig (BVTSelect @2 @3 @5 Proxy)
        (SBV.bvExtract @4 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 4) unboundedConfig (BVTSelect @0 @4 @5 Proxy)
        (SBV.bvExtract @3 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 4) unboundedConfig (BVTSelect @1 @4 @5 Proxy)
        (SBV.bvExtract @4 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig (BVTSelect @0 @5 @5 Proxy)
        id
    it "Extension lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 6) unboundedConfig (Zext @1 @5 @6 Proxy)
        SBV.zeroExtend
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 10) unboundedConfig (Zext @5 @5 @10 Proxy)
        SBV.zeroExtend
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 6) unboundedConfig (Sext @1 @5 @6 Proxy)
        SBV.signExtend
      testUnaryOpLowering' @(SignedBV 5) @(SignedBV 10) unboundedConfig (Sext @5 @5 @10 Proxy)
        SBV.signExtend
    it "Concat should work" $ do
      testBinaryOpLowering' @(SignedBV 4) @(SignedBV 5) @(SignedBV 9) unboundedConfig
        (BVTConcat @4 @5 @9) (SBV.#)

    it "AndBits lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig (AndBits @(SignedBV 5)) (.&.)
    it "OrBits lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig (OrBits @(SignedBV 5)) (.|.)
    it "XorBits lowering should work" $ do
      testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) unboundedConfig (XorBits @(SignedBV 5)) xor
    it "ComplementBits lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ComplementBits @(SignedBV 5)) complement
    it "ShiftBits lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 0) id
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 1) (`shift` 1)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 2) (`shift` 2)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 3) (`shift` 3)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 4) (`shift` 4)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 5) (`shift` 5)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) 5) (const 0)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) $ -1) (`shift` (-1))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) $ -2) (`shift` (-2))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) $ -3) (`shift` (-3))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) $ -4) (`shift` (-4))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) $ -5) (`shift` (-5))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (ShiftBits @(SignedBV 5) $ -5)
        (\x -> SBV.ite (x SBV..>= 0) 0 (-1))
    it "RotateBits lowering should work" $ do
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 0) id
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 1) (`rotate` 1)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 2) (`rotate` 2)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 3) (`rotate` 3)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 4) (`rotate` 4)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 5) (`rotate` 5)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) 5) id
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -1) (`rotate` (-1))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -1) (`rotate` 4)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -2) (`rotate` (-2))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -2) (`rotate` 3)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -3) (`rotate` (-3))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -3) (`rotate` 2)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -4) (`rotate` (-4))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -4) (`rotate` 1)
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -5) (`rotate` (-5))
      testUnaryOpLowering' @(SignedBV 5) unboundedConfig (RotateBits @(SignedBV 5) $ -5) id

  describe "Test UnsignedBV Lowering" $ do
    it "Add lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig (AddNum @(UnsignedBV 5)) (+)
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5)
        unboundedConfig
        (AddNum @(UnsignedBV 5))
        (\x y -> (x + 1) * (y + 1) - x * y - 1)
    it "Uminus lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig UMinusNum negate
      testUnaryOpLowering' @(UnsignedBV 5)
        unboundedConfig
        UMinusNum
        (\x -> (x + 1) * (x + 1) - 3 * x - x * x - 1)
    it "Abs lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig AbsNum abs
    it "Signum lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig SignumNum signum
    it "Times lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig TimesNum (*)
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5)
        unboundedConfig
        TimesNum
        (\x y -> (x + 1) * (y + 1) - x - y - 1)
    it "Lt lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig LTNum (SBV..<)
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5)
        unboundedConfig
        LTNum
        (\x y -> x * 2 - x SBV..< y * 2 - y)
    it "Le lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig LENum (SBV..<=)
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5)
        unboundedConfig
        LENum
        (\x y -> x * 2 - x SBV..<= y * 2 - y)
    it "Extract lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 1) unboundedConfig (BVTSelect @0 @1 @5 Proxy)
        (SBV.bvExtract @0 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 1) unboundedConfig (BVTSelect @1 @1 @5 Proxy)
        (SBV.bvExtract @1 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 1) unboundedConfig (BVTSelect @2 @1 @5 Proxy)
        (SBV.bvExtract @2 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 1) unboundedConfig (BVTSelect @3 @1 @5 Proxy)
        (SBV.bvExtract @3 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 1) unboundedConfig (BVTSelect @4 @1 @5 Proxy)
        (SBV.bvExtract @4 @4 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 2) unboundedConfig (BVTSelect @0 @2 @5 Proxy)
        (SBV.bvExtract @1 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 2) unboundedConfig (BVTSelect @1 @2 @5 Proxy)
        (SBV.bvExtract @2 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 2) unboundedConfig (BVTSelect @2 @2 @5 Proxy)
        (SBV.bvExtract @3 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 2) unboundedConfig (BVTSelect @3 @2 @5 Proxy)
        (SBV.bvExtract @4 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 3) unboundedConfig (BVTSelect @0 @3 @5 Proxy)
        (SBV.bvExtract @2 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 3) unboundedConfig (BVTSelect @1 @3 @5 Proxy)
        (SBV.bvExtract @3 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 3) unboundedConfig (BVTSelect @2 @3 @5 Proxy)
        (SBV.bvExtract @4 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 4) unboundedConfig (BVTSelect @0 @4 @5 Proxy)
        (SBV.bvExtract @3 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 4) unboundedConfig (BVTSelect @1 @4 @5 Proxy)
        (SBV.bvExtract @4 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig (BVTSelect @0 @5 @5 Proxy)
        id
    it "Extension lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 6) unboundedConfig (Zext @1 @5 @6 Proxy)
        SBV.zeroExtend
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 10) unboundedConfig (Zext @5 @5 @10 Proxy)
        SBV.zeroExtend
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 6) unboundedConfig (Sext @1 @5 @6 Proxy)
        SBV.signExtend
      testUnaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 10) unboundedConfig (Sext @5 @5 @10 Proxy)
        SBV.signExtend
    it "Concat should work" $ do
      testBinaryOpLowering' @(UnsignedBV 4) @(UnsignedBV 5) @(UnsignedBV 9) unboundedConfig
        (BVTConcat @4 @5 @9) (SBV.#)
    it "AndBits lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig (AndBits @(UnsignedBV 5)) (.&.)
    it "OrBits lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig (OrBits @(UnsignedBV 5)) (.|.)
    it "XorBits lowering should work" $ do
      testBinaryOpLowering' @(UnsignedBV 5) @(UnsignedBV 5) unboundedConfig (XorBits @(UnsignedBV 5)) xor
    it "ComplementBits lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ComplementBits @(UnsignedBV 5)) complement
    it "ShiftBits lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 0) id
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 1) (`shift` 1)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 2) (`shift` 2)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 3) (`shift` 3)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 4) (`shift` 4)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 5) (`shift` 5)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) 5) (const 0)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) $ -1) (`shift` (-1))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) $ -2) (`shift` (-2))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) $ -3) (`shift` (-3))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) $ -4) (`shift` (-4))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) $ -5) (`shift` (-5))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (ShiftBits @(UnsignedBV 5) $ -5)
        (\x -> SBV.ite (x SBV..>= 0) 0 (-1))
    it "RotateBits lowering should work" $ do
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 0) id
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 1) (`rotate` 1)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 2) (`rotate` 2)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 3) (`rotate` 3)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 4) (`rotate` 4)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 5) (`rotate` 5)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) 5) id
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -1) (`rotate` (-1))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -1) (`rotate` 4)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -2) (`rotate` (-2))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -2) (`rotate` 3)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -3) (`rotate` (-3))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -3) (`rotate` 2)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -4) (`rotate` (-4))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -4) (`rotate` 1)
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -5) (`rotate` (-5))
      testUnaryOpLowering' @(UnsignedBV 5) unboundedConfig (RotateBits @(UnsignedBV 5) $ -5) id

{-
it "DivI lowering should work" $ do
  testBinaryOpLowering' @Integer @Integer unboundedConfig DivI SBV.sDiv
it "ModI lowering should work" $ do
  testBinaryOpLowering' @(SignedBV 5) @(SignedBV 5) @(SignedBV 5) unboundedConfig ModI SBV.sMod
  -}
