{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Backend.SBV.Data.SMT.LoweringSpec where

import Control.Monad.Trans
import Data.Bits
import Data.Dynamic
import qualified Data.HashMap.Strict as M
import Data.Proxy
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBV
import Grisette.Backend.SBV.Data.SMT.Config
import Grisette.Backend.SBV.Data.SMT.Lowering
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.Prim.BV
import Grisette.IR.SymPrim.Data.Prim.Bits
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.Integer
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
import Grisette.IR.SymPrim.Data.Prim.Num
import Test.Hspec

testUnaryOpLowering ::
  forall a b as n.
  ( HasCallStack,
    SupportedPrim a,
    SBV.EqSymbolic (TermTy n b),
    Typeable (TermTy n a),
    SBV.SymVal as,
    TermTy n a ~ SBV.SBV as,
    Show as
  ) =>
  GrisetteSMTConfig n ->
  (Term a -> Term b) ->
  String ->
  (TermTy n a -> TermTy n b) ->
  Expectation
testUnaryOpLowering config f name sbvfun = do
  let a :: Term a = ssymbTerm "a"
  let fa :: Term b = f a
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
          _ -> lift $ expectationFailure $ "Lowering for " ++ name ++ " generated unsolvable formula"
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
          _ -> lift $ expectationFailure $ "Lowering for " ++ name ++ " generated unknown formula"

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
testUnaryOpLowering' config t sbvfun = testUnaryOpLowering @a @b @as config (constructUnary t) (show t) sbvfun

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
      testUnaryOpLowering @Bool @Bool unboundedConfig notTerm "not" SBV.sNot
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
  describe "Test IntN Lowering" $ do
    it "Add lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig (AddNum @(IntN 5)) (+)
      testBinaryOpLowering' @(IntN 5) @(IntN 5)
        unboundedConfig
        (AddNum @(IntN 5))
        (\x y -> (x + 1) * (y + 1) - x * y - 1)
    it "Uminus lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) unboundedConfig UMinusNum negate
      testUnaryOpLowering' @(IntN 5)
        unboundedConfig
        UMinusNum
        (\x -> (x + 1) * (x + 1) - 3 * x - x * x - 1)
    it "Abs lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) unboundedConfig AbsNum abs
    it "Signum lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) unboundedConfig SignumNum signum
    it "Times lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig TimesNum (*)
      testBinaryOpLowering' @(IntN 5) @(IntN 5)
        unboundedConfig
        TimesNum
        (\x y -> (x + 1) * (y + 1) - x - y - 1)
    it "Lt lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig LTNum (SBV..<)
      testBinaryOpLowering' @(IntN 5) @(IntN 5)
        unboundedConfig
        LTNum
        (\x y -> x * 2 - x SBV..< y * 2 - y)
    it "Le lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig LENum (SBV..<=)
      testBinaryOpLowering' @(IntN 5) @(IntN 5)
        unboundedConfig
        LENum
        (\x y -> x * 2 - x SBV..<= y * 2 - y)
    it "Extract lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) @(IntN 1)
        unboundedConfig
        (BVTSelect @IntN @0 @1 @5 Proxy)
        (SBV.bvExtract @0 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 1)
        unboundedConfig
        (BVTSelect @IntN @1 @1 @5 Proxy)
        (SBV.bvExtract @1 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 1)
        unboundedConfig
        (BVTSelect @IntN @2 @1 @5 Proxy)
        (SBV.bvExtract @2 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 1)
        unboundedConfig
        (BVTSelect @IntN @3 @1 @5 Proxy)
        (SBV.bvExtract @3 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 1)
        unboundedConfig
        (BVTSelect @IntN @4 @1 @5 Proxy)
        (SBV.bvExtract @4 @4 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 2)
        unboundedConfig
        (BVTSelect @IntN @0 @2 @5 Proxy)
        (SBV.bvExtract @1 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 2)
        unboundedConfig
        (BVTSelect @IntN @1 @2 @5 Proxy)
        (SBV.bvExtract @2 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 2)
        unboundedConfig
        (BVTSelect @IntN @2 @2 @5 Proxy)
        (SBV.bvExtract @3 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 2)
        unboundedConfig
        (BVTSelect @IntN @3 @2 @5 Proxy)
        (SBV.bvExtract @4 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 3)
        unboundedConfig
        (BVTSelect @IntN @0 @3 @5 Proxy)
        (SBV.bvExtract @2 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 3)
        unboundedConfig
        (BVTSelect @IntN @1 @3 @5 Proxy)
        (SBV.bvExtract @3 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 3)
        unboundedConfig
        (BVTSelect @IntN @2 @3 @5 Proxy)
        (SBV.bvExtract @4 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 4)
        unboundedConfig
        (BVTSelect @IntN @0 @4 @5 Proxy)
        (SBV.bvExtract @3 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 4)
        unboundedConfig
        (BVTSelect @IntN @1 @4 @5 Proxy)
        (SBV.bvExtract @4 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(IntN 5) @(IntN 5)
        unboundedConfig
        (BVTSelect @IntN @0 @5 @5 Proxy)
        id
    it "Extension lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) @(IntN 6)
        unboundedConfig
        (Zext @IntN @5 @6)
        SBV.zeroExtend
      testUnaryOpLowering' @(IntN 5) @(IntN 10)
        unboundedConfig
        (Zext @IntN @5 @10)
        SBV.zeroExtend
      testUnaryOpLowering' @(IntN 5) @(IntN 6)
        unboundedConfig
        (Sext @IntN @5 @6)
        SBV.signExtend
      testUnaryOpLowering' @(IntN 5) @(IntN 10)
        unboundedConfig
        (Sext @IntN @5 @10)
        SBV.signExtend
    it "Concat should work" $ do
      testBinaryOpLowering' @(IntN 4) @(IntN 5) @(IntN 9)
        unboundedConfig
        (BVTConcat @IntN @4 @5 @9)
        (SBV.#)

    it "AndBits lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig (AndBits @(IntN 5)) (.&.)
    it "OrBits lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig (OrBits @(IntN 5)) (.|.)
    it "XorBits lowering should work" $ do
      testBinaryOpLowering' @(IntN 5) @(IntN 5) unboundedConfig (XorBits @(IntN 5)) xor
    it "ComplementBits lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ComplementBits @(IntN 5)) complement
    it "ShiftBits lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 0) id
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 1) (`shift` 1)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 2) (`shift` 2)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 3) (`shift` 3)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 4) (`shift` 4)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 5) (`shift` 5)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) 5) (const 0)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) $ -1) (`shift` (-1))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) $ -2) (`shift` (-2))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) $ -3) (`shift` (-3))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) $ -4) (`shift` (-4))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (ShiftBits @(IntN 5) $ -5) (`shift` (-5))
      testUnaryOpLowering' @(IntN 5)
        unboundedConfig
        (ShiftBits @(IntN 5) $ -5)
        (\x -> SBV.ite (x SBV..>= 0) 0 (-1))
    it "RotateBits lowering should work" $ do
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 0) id
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 1) (`rotate` 1)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 2) (`rotate` 2)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 3) (`rotate` 3)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 4) (`rotate` 4)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 5) (`rotate` 5)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) 5) id
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -1) (`rotate` (-1))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -1) (`rotate` 4)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -2) (`rotate` (-2))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -2) (`rotate` 3)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -3) (`rotate` (-3))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -3) (`rotate` 2)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -4) (`rotate` (-4))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -4) (`rotate` 1)
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -5) (`rotate` (-5))
      testUnaryOpLowering' @(IntN 5) unboundedConfig (RotateBits @(IntN 5) $ -5) id

  describe "Test WordN Lowering" $ do
    it "Add lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig (AddNum @(WordN 5)) (+)
      testBinaryOpLowering' @(WordN 5) @(WordN 5)
        unboundedConfig
        (AddNum @(WordN 5))
        (\x y -> (x + 1) * (y + 1) - x * y - 1)
    it "Uminus lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) unboundedConfig UMinusNum negate
      testUnaryOpLowering' @(WordN 5)
        unboundedConfig
        UMinusNum
        (\x -> (x + 1) * (x + 1) - 3 * x - x * x - 1)
    it "Abs lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) unboundedConfig AbsNum abs
    it "Signum lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) unboundedConfig SignumNum signum
    it "Times lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig TimesNum (*)
      testBinaryOpLowering' @(WordN 5) @(WordN 5)
        unboundedConfig
        TimesNum
        (\x y -> (x + 1) * (y + 1) - x - y - 1)
    it "Lt lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig LTNum (SBV..<)
      testBinaryOpLowering' @(WordN 5) @(WordN 5)
        unboundedConfig
        LTNum
        (\x y -> x * 2 - x SBV..< y * 2 - y)
    it "Le lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig LENum (SBV..<=)
      testBinaryOpLowering' @(WordN 5) @(WordN 5)
        unboundedConfig
        LENum
        (\x y -> x * 2 - x SBV..<= y * 2 - y)
    it "Extract lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) @(WordN 1)
        unboundedConfig
        (BVTSelect @WordN @0 @1 @5 Proxy)
        (SBV.bvExtract @0 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 1)
        unboundedConfig
        (BVTSelect @WordN @1 @1 @5 Proxy)
        (SBV.bvExtract @1 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 1)
        unboundedConfig
        (BVTSelect @WordN @2 @1 @5 Proxy)
        (SBV.bvExtract @2 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 1)
        unboundedConfig
        (BVTSelect @WordN @3 @1 @5 Proxy)
        (SBV.bvExtract @3 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 1)
        unboundedConfig
        (BVTSelect @WordN @4 @1 @5 Proxy)
        (SBV.bvExtract @4 @4 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 2)
        unboundedConfig
        (BVTSelect @WordN @0 @2 @5 Proxy)
        (SBV.bvExtract @1 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 2)
        unboundedConfig
        (BVTSelect @WordN @1 @2 @5 Proxy)
        (SBV.bvExtract @2 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 2)
        unboundedConfig
        (BVTSelect @WordN @2 @2 @5 Proxy)
        (SBV.bvExtract @3 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 2)
        unboundedConfig
        (BVTSelect @WordN @3 @2 @5 Proxy)
        (SBV.bvExtract @4 @3 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 3)
        unboundedConfig
        (BVTSelect @WordN @0 @3 @5 Proxy)
        (SBV.bvExtract @2 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 3)
        unboundedConfig
        (BVTSelect @WordN @1 @3 @5 Proxy)
        (SBV.bvExtract @3 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 3)
        unboundedConfig
        (BVTSelect @WordN @2 @3 @5 Proxy)
        (SBV.bvExtract @4 @2 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 4)
        unboundedConfig
        (BVTSelect @WordN @0 @4 @5 Proxy)
        (SBV.bvExtract @3 @0 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 4)
        unboundedConfig
        (BVTSelect @WordN @1 @4 @5 Proxy)
        (SBV.bvExtract @4 @1 @5 Proxy Proxy)
      testUnaryOpLowering' @(WordN 5) @(WordN 5)
        unboundedConfig
        (BVTSelect @WordN @0 @5 @5 Proxy)
        id
    it "Extension lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) @(WordN 6)
        unboundedConfig
        (Zext @WordN @5 @6)
        SBV.zeroExtend
      testUnaryOpLowering' @(WordN 5) @(WordN 10)
        unboundedConfig
        (Zext @WordN @5 @10)
        SBV.zeroExtend
      testUnaryOpLowering' @(WordN 5) @(WordN 6)
        unboundedConfig
        (Sext @WordN @5 @6)
        SBV.signExtend
      testUnaryOpLowering' @(WordN 5) @(WordN 10)
        unboundedConfig
        (Sext @WordN @5 @10)
        SBV.signExtend
    it "Concat should work" $ do
      testBinaryOpLowering' @(WordN 4) @(WordN 5) @(WordN 9)
        unboundedConfig
        (BVTConcat @WordN @4 @5 @9)
        (SBV.#)
    it "AndBits lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig (AndBits @(WordN 5)) (.&.)
    it "OrBits lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig (OrBits @(WordN 5)) (.|.)
    it "XorBits lowering should work" $ do
      testBinaryOpLowering' @(WordN 5) @(WordN 5) unboundedConfig (XorBits @(WordN 5)) xor
    it "ComplementBits lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ComplementBits @(WordN 5)) complement
    it "ShiftBits lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 0) id
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 1) (`shift` 1)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 2) (`shift` 2)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 3) (`shift` 3)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 4) (`shift` 4)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 5) (`shift` 5)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) 5) (const 0)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) $ -1) (`shift` (-1))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) $ -2) (`shift` (-2))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) $ -3) (`shift` (-3))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) $ -4) (`shift` (-4))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (ShiftBits @(WordN 5) $ -5) (`shift` (-5))
      testUnaryOpLowering' @(WordN 5)
        unboundedConfig
        (ShiftBits @(WordN 5) $ -5)
        (\x -> SBV.ite (x SBV..>= 0) 0 (-1))
    it "RotateBits lowering should work" $ do
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 0) id
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 1) (`rotate` 1)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 2) (`rotate` 2)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 3) (`rotate` 3)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 4) (`rotate` 4)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 5) (`rotate` 5)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) 5) id
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -1) (`rotate` (-1))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -1) (`rotate` 4)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -2) (`rotate` (-2))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -2) (`rotate` 3)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -3) (`rotate` (-3))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -3) (`rotate` 2)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -4) (`rotate` (-4))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -4) (`rotate` 1)
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -5) (`rotate` (-5))
      testUnaryOpLowering' @(WordN 5) unboundedConfig (RotateBits @(WordN 5) $ -5) id

{-
it "DivI lowering should work" $ do
  testBinaryOpLowering' @Integer @Integer unboundedConfig DivI SBV.sDiv
it "ModI lowering should work" $ do
  testBinaryOpLowering' @(IntN 5) @(IntN 5) @(IntN 5) unboundedConfig ModI SBV.sMod
  -}
