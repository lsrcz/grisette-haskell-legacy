{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Backend.SBV.Data.SMT.Lowering
  ( lowerSinglePrim,
    lowerSinglePrim',
    parseModel,
    SymBiMap,
  )
where

import GHC.Stack
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Bits
import Data.Dynamic
import Data.Foldable
import Data.Kind
import Data.Maybe
import qualified Data.SBV as SBV
import qualified Data.SBV.Internals as SBVI
import Data.Type.Equality (type (~~))
import Data.Typeable
import GHC.Exts (sortWith)
import GHC.Natural
import GHC.TypeNats
import Grisette.Backend.SBV.Data.SMT.Config
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.GeneralFunc
import Grisette.IR.SymPrim.Data.Prim.BV
import Grisette.IR.SymPrim.Data.Prim.Bits
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.GeneralFunc
import Grisette.IR.SymPrim.Data.Prim.Integer
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.Prim.Model as PM
import Grisette.IR.SymPrim.Data.Prim.Num
import Grisette.IR.SymPrim.Data.Prim.TabularFunc
import Grisette.IR.SymPrim.Data.TabularFunc
import qualified Type.Reflection as R
import Unsafe.Coerce
import Grisette.Backend.SBV.Data.SMT.SymBiMap

newtype NatRepr (n :: Nat) = NatRepr Natural

withKnownNat :: forall n r. NatRepr n -> (KnownNat n => r) -> r
withKnownNat (NatRepr nVal) v =
  case someNatVal nVal of
    SomeNat (Proxy :: Proxy n') ->
      case unsafeAxiom :: n :~: n' of
        Refl -> v

data LeqProof (m :: Nat) (n :: Nat) where
  LeqProof :: m <= n => LeqProof m n

withLeqProof :: LeqProof m n -> ((m <= n) => a) -> a
withLeqProof p a = case p of LeqProof -> a

-- | Assert a proof of equality between two types.
-- This is unsafe if used improperly, so use this with caution!
unsafeAxiom :: forall a b. a :~: b
unsafeAxiom = unsafeCoerce (Refl @a)
{-# NOINLINE unsafeAxiom #-} -- Note [Mark unsafe axioms as NOINLINE]

cachedResult ::
  forall integerBitWidth a.
  (SupportedPrim a, Typeable (TermTy integerBitWidth a)) =>
  Term a ->
  State SymBiMap (Maybe (TermTy integerBitWidth a))
cachedResult t = gets $ \m -> do
  d <- lookupTerm (SomeTerm t) m
  Just $ fromDyn d undefined

addResult ::
  forall integerBitWidth a.
  (SupportedPrim a, Typeable (TermTy integerBitWidth a)) =>
  Term a ->
  TermTy integerBitWidth a ->
  State SymBiMap ()
addResult tm sbvtm = modify $ addBiMapIntermediate (SomeTerm tm) (toDyn sbvtm)

lowerSinglePrim' ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  (TermTy integerBitWidth a, SymBiMap)
lowerSinglePrim' config t = runState (lowerSinglePrimCached' config t)

lowerSinglePrimCached' ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  State SymBiMap (TermTy integerBitWidth a)
lowerSinglePrimCached' config t = introSupportedPrimConstraint t $
  case (config, R.typeRep @a) of
    ResolvedDeepType -> do
      r <- cachedResult @integerBitWidth t
      case r of
        Just v -> return v
        _ -> lowerSinglePrimImpl' config t
    _ -> translateTypeError (R.typeRep @a)

lowerUnaryTerm' ::
  forall integerBitWidth a a1 x x1.
  (Typeable x1, a1 ~ TermTy integerBitWidth a, SupportedPrim x, x1 ~ TermTy integerBitWidth x) =>
  GrisetteSMTConfig integerBitWidth ->
  Term x ->
  Term a ->
  (a1 -> x1) ->
  State SymBiMap (TermTy integerBitWidth x)
lowerUnaryTerm' config orig t1 f = do
  l1 <- lowerSinglePrimCached' config t1
  let g = f l1
  addResult @integerBitWidth orig g
  return g

lowerBinaryTerm' ::
  forall integerBitWidth a b a1 b1 x.
  (Typeable (TermTy integerBitWidth x), a1 ~ TermTy integerBitWidth a, b1 ~ TermTy integerBitWidth b, SupportedPrim x) =>
  GrisetteSMTConfig integerBitWidth ->
  Term x ->
  Term a ->
  Term b ->
  (a1 -> b1 -> (TermTy integerBitWidth x)) ->
  State SymBiMap (TermTy integerBitWidth x)
lowerBinaryTerm' config orig t1 t2 f = do
  l1 <- lowerSinglePrimCached' config t1
  l2 <- lowerSinglePrimCached' config t2
  let g = f l1 l2
  addResult @integerBitWidth orig g
  return g

lowerSinglePrimImpl' ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  State SymBiMap (TermTy integerBitWidth a)
lowerSinglePrimImpl' ResolvedConfig {} (ConcTerm _ v) =
  case R.typeRep @a of
    BoolType -> return $ if v then SBV.sTrue else SBV.sFalse
    IntegerType -> return $ fromInteger v
    SignedBVType _ -> case v of
      IntN x -> return $ fromInteger x
    UnsignedBVType _ -> case v of
      WordN x -> return $ fromInteger x
    _ -> translateTypeError (R.typeRep @a)
lowerSinglePrimImpl' _ t@SymbTerm {} =
  error $
    "The symbolic term should have already been lowered " ++ show t ++ " to SMT with collectedPrims.\n"
      ++ "We don't support adding new symbolics after collectedPrims with SBV backend"
lowerSinglePrimImpl' config@ResolvedConfig {} t@(UnaryTerm _ op (_ :: Term x)) =
  fromMaybe errorMsg $ asum [numType, bitsType, extBV, extractBV]
  where
    errorMsg :: forall t1. t1
    errorMsg = translateUnaryError (show op) (R.typeRep @x) (R.typeRep @a)
    numType :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    numType = case (config, R.typeRep @a) of
      ResolvedNumType ->
        case t of
          UMinusNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm' config t t1 (\x -> - x)
          SignumNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm' config t t1 signum
          AbsNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm' config t t1 abs
          _ -> Nothing
      _ -> Nothing
    bitsType :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    bitsType = case (config, R.typeRep @a) of
      ResolvedBitsType ->
        case t of
          ComplementBitsTerm (t1 :: Term a) -> Just $ lowerUnaryTerm' config t t1 complement
          ShiftBitsTerm (t1 :: Term a) i -> Just $ lowerUnaryTerm' config t t1 (`shift` i)
          RotateBitsTerm (t1 :: Term a) i -> Just $ lowerUnaryTerm' config t t1 (`rotate` i)
          _ -> Nothing
      _ -> Nothing
    extBV :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    extBV = case (R.typeRep @x, R.typeRep @a) of
      (UnsignedBVType (_ :: proxy xn), UnsignedBVType (_ :: proxy an)) ->
        case extensionView @WordN @xn @an t of
          Just (ExtensionMatchResult isSignedExt (t1 :: Term (WordN xn))) ->
            Just $
              bvIsNonZeroFromGEq1 @(an - xn) $
                lowerUnaryTerm' config t t1 (if isSignedExt then SBV.signExtend else SBV.zeroExtend)
          _ -> Nothing
      (SignedBVType (_ :: proxy xn), SignedBVType (_ :: proxy an)) ->
        case extensionView @IntN @xn @an t of
          Just (ExtensionMatchResult isSignedExt (t1 :: Term (IntN xn))) ->
            Just $
              bvIsNonZeroFromGEq1 @(an - xn) $
                -- bvIsNonZeroFromGEq1 @nn $
                lowerUnaryTerm' @integerBitWidth @x @(SBV.SBV (SBV.IntN xn)) @a @(SBV.SBV (SBV.IntN an))
                  config
                  t
                  t1
                  ( if isSignedExt
                      then SBV.signExtend
                      else \x ->
                        SBV.sFromIntegral
                          (SBV.zeroExtend (SBV.sFromIntegral x :: SBV.SBV (SBV.WordN xn)) :: SBV.SBV (SBV.WordN an))
                  )
          _ -> Nothing
      _ -> Nothing
    extractBV :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    extractBV = case (R.typeRep @x, R.typeRep @a) of
      (UnsignedBVType (_ :: proxy xn), UnsignedBVType (_ :: proxy an)) ->
        case selectView @WordN @an @xn t of
          Just (SelectMatchResult (_ :: proxy1 ix) (t1 :: Term (WordN xn))) ->
            Just $
              ev @ix @an @xn $
                lowerUnaryTerm' config t t1 (SBV.bvExtract (Proxy @(an + ix - 1)) (Proxy @ix))
          _ -> Nothing
      (SignedBVType (_ :: proxy xn), SignedBVType (_ :: proxy an)) ->
        case selectView @IntN @an @xn t of
          Just (SelectMatchResult (_ :: proxy1 ix) (t1 :: Term (IntN xn))) ->
            Just $
              ev @ix @an @xn $
                lowerUnaryTerm' config t t1 (SBV.bvExtract (Proxy @(an + ix - 1)) (Proxy @ix))
          _ -> Nothing
      _ -> Nothing
      where
        ev ::
          forall ix w ow r.
          ( KnownNat ix,
            KnownNat w,
            KnownNat ow,
            ix + w <= ow,
            1 <= ow,
            1 <= w
          ) =>
          ( ( ((((w + ix) - 1) - ix) + 1) ~ w,
              KnownNat ((w + ix) - 1),
              (((w + ix) - 1) + 1) <= ow,
              ix <= ((w + ix) - 1)
            ) =>
            r
          ) ->
          r
        ev r =
          let withEquality :: forall x1 x2 x3. x1 :~: x2 -> (x1 ~ x2 => x3) -> x3
              withEquality Refl ret = ret
              wpixm1repr :: NatRepr (w + ix - 1) = NatRepr (natVal (Proxy @w) + natVal (Proxy @ix) - 1)
              wpixleqow :: LeqProof (w + ix) ow = unsafeCoerce (LeqProof :: LeqProof 0 0)
              wpixm1p1cancel :: (((w + ix) - 1) + 1) :~: (w + ix) = unsafeCoerce (LeqProof :: LeqProof 0 0)
              ev1 :: LeqProof ix ((w + ix) - 1) = unsafeCoerce (LeqProof :: LeqProof 0 0)
           in withKnownNat wpixm1repr $
                withLeqProof wpixleqow $
                  withEquality wpixm1p1cancel $
                    withEquality (unsafeAxiom :: ((((w + ix) - 1) - ix) + 1) :~: w) $
                      withLeqProof ev1 r
lowerSinglePrimImpl' config@ResolvedConfig {} t@(BinaryTerm _ op (_ :: Term x) (_ :: Term y)) =
  fromMaybe errorMsg $ asum [numType, numOrdCmp, bitsType, concatBV, funcApply]
  where
    errorMsg :: forall t1. t1
    errorMsg = translateBinaryError (show op) (R.typeRep @x) (R.typeRep @y) (R.typeRep @a)
    numOrdCmp :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    numOrdCmp = case (R.typeRep @a, (config, R.typeRep @x)) of
      (BoolType, ResolvedNumOrdType) -> case t of
        LTNumTerm (t1' :: Term x) t2' -> Just $ lowerBinaryTerm' config t t1' t2' (SBV..<)
        LENumTerm (t1' :: Term x) t2' -> Just $ lowerBinaryTerm' config t t1' t2' (SBV..<=)
        _ -> Nothing
      _ -> Nothing
    numType :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    numType = case (config, R.typeRep @a) of
      ResolvedNumType ->
        case t of
          TimesNumTerm (t1' :: Term a) t2' -> Just $ lowerBinaryTerm' config t t1' t2' (*)
          _ -> Nothing
      _ -> Nothing
    bitsType :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    bitsType = case (config, R.typeRep @a) of
      ResolvedBitsType ->
        case t of
          AndBitsTerm (t1 :: Term a) t2 -> Just $ lowerBinaryTerm' config t t1 t2 (.&.)
          OrBitsTerm (t1 :: Term a) t2 -> Just $ lowerBinaryTerm' config t t1 t2 (.|.)
          XorBitsTerm (t1 :: Term a) t2 -> Just $ lowerBinaryTerm' config t t1 t2 xor
          _ -> Nothing
      _ -> Nothing
    funcApply :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    funcApply = case (config, R.typeRep @a) of
      ResolvedDeepType -> Just $
        case t of
          ApplyFTerm (t1' :: Term (y =-> a)) (t2' :: Term y) -> do
            l1 <- lowerSinglePrimCached' config t1'
            l2 <- lowerSinglePrimCached' config t2'
            let g = l1 l2
            addResult @integerBitWidth t g
            return g
          ApplyGTerm (t1' :: Term (y --> a)) (t2' :: Term y) -> do
            l1 <- lowerSinglePrimCached' config t1'
            l2 <- lowerSinglePrimCached' config t2'
            let g = l1 l2
            addResult @integerBitWidth t g
            return g
          _ -> errorMsg
      _ -> Nothing
    concatBV :: Maybe (State SymBiMap (TermTy integerBitWidth a))
    concatBV = case (R.typeRep @x, R.typeRep @y, R.typeRep @a) of
      (UnsignedBVType (_ :: proxy xn), UnsignedBVType (_ :: proxy yn), UnsignedBVType (_ :: proxy an)) ->
        case concatView @WordN @xn @yn @an t of
          Just (ConcatMatchResult (t1 :: Term (WordN xn)) (t2 :: Term (WordN yn))) ->
            Just $ lowerBinaryTerm' config t t1 t2 (SBV.#)
          _ -> Nothing
      (SignedBVType (_ :: proxy xn), SignedBVType (_ :: proxy yn), SignedBVType (_ :: proxy an)) ->
        case concatView @IntN @xn @yn @an t of
          Just (ConcatMatchResult (t1 :: Term (IntN xn)) (t2 :: Term (IntN yn))) ->
            Just $
              lowerBinaryTerm'
                config
                t
                t1
                t2
                ( \(x :: SBV.SInt xn) (y :: SBV.SInt yn) ->
                    SBV.sFromIntegral $
                      (SBV.sFromIntegral x :: SBV.SWord xn) SBV.# (SBV.sFromIntegral y :: SBV.SWord yn)
                )
          _ -> Nothing
      _ -> Nothing
lowerSinglePrimImpl' ResolvedConfig {} (TernaryTerm _ op (_ :: Term x) (_ :: Term y) (_ :: Term z)) = errorMsg
  where
    errorMsg :: forall t1. t1
    errorMsg = translateTernaryError (show op) (R.typeRep @x) (R.typeRep @y) (R.typeRep @z) (R.typeRep @a)
lowerSinglePrimImpl' config t@(NotTerm _ arg) = lowerUnaryTerm' config t arg SBV.sNot
lowerSinglePrimImpl' config t@(OrTerm _ arg1 arg2) = lowerBinaryTerm' config t arg1 arg2 (SBV..||)
lowerSinglePrimImpl' config t@(AndTerm _ arg1 arg2) = lowerBinaryTerm' config t arg1 arg2 (SBV..&&)
lowerSinglePrimImpl' config t@(EqvTerm _ (arg1 :: Term x) arg2) =
  case (config, R.typeRep @x) of
    ResolvedSimpleType -> lowerBinaryTerm' config t arg1 arg2 (SBV..==)
    _ -> translateBinaryError "(==)" (R.typeRep @x) (R.typeRep @x) (R.typeRep @a)
lowerSinglePrimImpl' config t@(ITETerm _ cond arg1 arg2) =
  case (config, R.typeRep @a) of
    ResolvedSimpleType -> do
          l1 <- lowerSinglePrimCached' config cond
          l2 <- lowerSinglePrimCached' config arg1
          l3 <- lowerSinglePrimCached' config arg2
          let g = SBV.ite l1 l2 l3
          addResult @integerBitWidth t g
          return g
    _ -> translateTernaryError "ite" (R.typeRep @Bool) (R.typeRep @a) (R.typeRep @a) (R.typeRep @a)
lowerSinglePrimImpl' config t@(AddNumTerm _ arg1 arg2) =
  case (config, R.typeRep @a) of
    ResolvedNumType -> lowerBinaryTerm' config t arg1 arg2 (+)
    _ -> translateBinaryError "(+)" (R.typeRep @a) (R.typeRep @a) (R.typeRep @a)
lowerSinglePrimImpl' _ _ = undefined

buildUTFunc11 ::
  forall integerBitWidth s1 s2 a.
  (SupportedPrim a, SupportedPrim s1, SupportedPrim s2) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 =-> s2)))
buildUTFunc11 config ta tb term@(SymbTerm _ ts) m = case ((config, ta), (config, tb)) of
  (ResolvedSimpleType, ResolvedSimpleType) ->
    let name = "ufunc_" ++ show (sizeBiMap m)
        f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2) name
     in Just $ return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
  _ -> Nothing
buildUTFunc11 _ _ _ _ _ = error "Should only be called on SymbTerm"

buildUTFunc111 ::
  forall integerBitWidth s1 s2 s3 a.
  (SupportedPrim a, SupportedPrim s1, SupportedPrim s2, SupportedPrim s3) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  R.TypeRep s3 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 =-> s2 =-> s3)))
buildUTFunc111 config ta tb tc term@(SymbTerm _ ts) m = case ((config, ta), (config, tb), (config, tc)) of
  (ResolvedSimpleType, ResolvedSimpleType, ResolvedSimpleType) ->
    let name = "ufunc_" ++ show (sizeBiMap m)
        f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2 -> TermTy integerBitWidth s3) name
     in Just $ return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
  _ -> Nothing
buildUTFunc111 _ _ _ _ _ _ = error "Should only be called on SymbTerm"

buildUGFunc11 ::
  forall integerBitWidth s1 s2 a.
  (SupportedPrim a, SupportedPrim s1, SupportedPrim s2) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 --> s2)))
buildUGFunc11 config ta tb term@(SymbTerm _ ts) m = case ((config, ta), (config, tb)) of
  (ResolvedSimpleType, ResolvedSimpleType) ->
    let name = "ufunc_" ++ show (sizeBiMap m)
        f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2) name
     in Just $ return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
  _ -> Nothing
buildUGFunc11 _ _ _ _ _ = error "Should only be called on SymbTerm"

buildUGFunc111 ::
  forall integerBitWidth s1 s2 s3 a.
  (SupportedPrim a, SupportedPrim s1, SupportedPrim s2, SupportedPrim s3) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  R.TypeRep s3 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 --> s2 --> s3)))
buildUGFunc111 config ta tb tc term@(SymbTerm _ ts) m = case ((config, ta), (config, tb), (config, tc)) of
  (ResolvedSimpleType, ResolvedSimpleType, ResolvedSimpleType) ->
    let name = "ufunc_" ++ show (sizeBiMap m)
        f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2 -> TermTy integerBitWidth s3) name
     in Just $ return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
  _ -> Nothing
buildUGFunc111 _ _ _ _ _ _ = error "Should only be called on SymbTerm"

lowerSinglePrimUFunc ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
lowerSinglePrimUFunc config t@(SymbTerm _ _) m =
  case R.typeRep @a of
    TFun3Type (t1 :: R.TypeRep a1) (t2 :: R.TypeRep a2) (t3 :: R.TypeRep a3) -> buildUTFunc111 config t1 t2 t3 t m
    TFunType (ta :: R.TypeRep b) (tb :: R.TypeRep b1) -> buildUTFunc11 config ta tb t m
    GFun3Type (t1 :: R.TypeRep a1) (t2 :: R.TypeRep a2) (t3 :: R.TypeRep a3) -> buildUGFunc111 config t1 t2 t3 t m
    GFunType (ta :: R.TypeRep b) (tb :: R.TypeRep b1) -> buildUGFunc11 config ta tb t m
    _ -> Nothing
lowerSinglePrimUFunc _ _ _ = error "Should not call this function"

lowerUnaryTerm ::
  forall integerBitWidth a a1 x x1. 
  (Typeable x1, a1 ~ TermTy integerBitWidth a, SupportedPrim x, HasCallStack) =>
  GrisetteSMTConfig integerBitWidth ->
  Term x ->
  Term a ->
  (a1 -> x1) ->
  SymBiMap ->
  SBV.Symbolic (SymBiMap, x1)
lowerUnaryTerm config orig t1 f m = do
  (m1, l1) <- lowerSinglePrimCached config t1 m
  let g = f l1
  return (addBiMapIntermediate (SomeTerm orig) (toDyn g) m1, g)

lowerBinaryTerm ::
  forall integerBitWidth a b a1 b1 x x1.
  (Typeable x1, a1 ~ TermTy integerBitWidth a, b1 ~ TermTy integerBitWidth b, SupportedPrim x, HasCallStack) =>
  GrisetteSMTConfig integerBitWidth ->
  Term x ->
  Term a ->
  Term b ->
  (a1 -> b1 -> x1) ->
  SymBiMap ->
  SBV.Symbolic (SymBiMap, x1)
lowerBinaryTerm config orig t1 t2 f m = do
  (m1, l1) <- lowerSinglePrimCached config t1 m
  (m2, l2) <- lowerSinglePrimCached config t2 m1
  let g = f l1 l2
  return (addBiMapIntermediate (SomeTerm orig) (toDyn g) m2, g)

lowerSinglePrimCached ::
  forall integerBitWidth a. HasCallStack =>
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)
lowerSinglePrimCached config t m =
  introSupportedPrimConstraint t $
    case (config, R.typeRep @a) of
      ResolvedDeepType ->
        case lookupTerm (SomeTerm t) m of
          Just x -> return (m, fromDyn x undefined)
          Nothing -> lowerSinglePrimImpl config t m
      _ -> translateTypeError (R.typeRep @a)

lowerSinglePrim ::
  forall integerBitWidth a. HasCallStack =>
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)
lowerSinglePrim config t = lowerSinglePrimCached config t emptySymBiMap

translateTypeError :: HasCallStack => R.TypeRep a -> b
translateTypeError ta = error $
  "Don't know how to translate the type " ++ show ta ++ " to SMT"

translateUnaryError :: HasCallStack => String -> R.TypeRep a -> R.TypeRep b -> c
translateUnaryError op ta tb = error $
  "Don't know how to translate the op " ++ show op ++ " :: "
    ++ show ta ++ " -> " ++ show tb ++ " to SMT"

translateBinaryError :: HasCallStack => String -> R.TypeRep a -> R.TypeRep b -> R.TypeRep c -> d
translateBinaryError op ta tb tc = error $
  "Don't know how to translate the op " ++ show op ++ " :: "
    ++ show ta ++ " -> " ++ show tb ++ " -> " ++ show tc ++ " to SMT"

translateTernaryError :: HasCallStack => String -> R.TypeRep a -> R.TypeRep b -> R.TypeRep c -> R.TypeRep d -> e
translateTernaryError op ta tb tc td = error $
  "Don't know how to translate the op " ++ show op ++ " :: "
    ++ show ta ++ " -> " ++ show tb ++ " -> " ++ show tc ++ " -> " ++ show td ++ " to SMT"

lowerSinglePrimImpl ::
  forall integerBitWidth a. HasCallStack =>
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)
lowerSinglePrimImpl ResolvedConfig {} (ConcTerm _ v) m =
  case R.typeRep @a of
    BoolType -> return (m, if v then SBV.sTrue else SBV.sFalse)
    IntegerType -> return (m, fromInteger v)
    SignedBVType _ -> case v of
      IntN x -> return (m, fromInteger x)
    UnsignedBVType _ -> case v of
      WordN x -> return (m, fromInteger x)
    _ -> translateTypeError (R.typeRep @a)
lowerSinglePrimImpl config t@(SymbTerm _ ts) m =
  fromMaybe errorMsg $ asum [simple, ufunc]
  where
    errorMsg :: forall x. x
    errorMsg = translateTypeError (R.typeRep @a)
    simple :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    simple = case (config, R.typeRep @a) of
      ResolvedSimpleType -> Just $ do
        let name = show ts
        (g :: TermTy integerBitWidth a) <- SBV.free name
        return (addBiMap (SomeTerm t) (toDyn g) name ts m, g)
      _ -> Nothing
    ufunc :: (Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)))
    ufunc = lowerSinglePrimUFunc config t m
lowerSinglePrimImpl config@ResolvedConfig {} t@(UnaryTerm _ op (_ :: Term x)) m =
  fromMaybe errorMsg $ asum [numType, bitsType, extBV, extractBV]
  where
    errorMsg :: forall t1. t1
    errorMsg = translateUnaryError (show op) (R.typeRep @x) (R.typeRep @a)
    numType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    numType = case (config, R.typeRep @a) of
      ResolvedNumType ->
        case t of
          UMinusNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 (\x -> - x) m
          SignumNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 signum m
          AbsNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 abs m
          _ -> Nothing
      _ -> Nothing
    bitsType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    bitsType = case (config, R.typeRep @a) of
      ResolvedBitsType ->
        case t of
          ComplementBitsTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 complement m
          ShiftBitsTerm (t1 :: Term a) i -> Just $ lowerUnaryTerm config t t1 (`shift` i) m
          RotateBitsTerm (t1 :: Term a) i -> Just $ lowerUnaryTerm config t t1 (`rotate` i) m
          _ -> Nothing
      _ -> Nothing
    extBV :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    extBV = case (R.typeRep @x, R.typeRep @a) of
      (UnsignedBVType (_ :: proxy xn), UnsignedBVType (_ :: proxy an)) ->
        case extensionView @WordN @xn @an t of
          Just (ExtensionMatchResult isSignedExt (t1 :: Term (WordN xn))) ->
            Just $
              bvIsNonZeroFromGEq1 @(an - xn) $
                -- bvIsNonZeroFromGEq1 @nn $
                lowerUnaryTerm config t t1 (if isSignedExt then SBV.signExtend else SBV.zeroExtend) m
          _ -> Nothing
      (SignedBVType (_ :: proxy xn), SignedBVType (_ :: proxy an)) ->
        case extensionView @IntN @xn @an t of
          Just (ExtensionMatchResult isSignedExt (t1 :: Term (IntN xn))) ->
            Just $
              -- bvIsNonZeroFromGEq1 @nn $
              bvIsNonZeroFromGEq1 @(an - xn) $
                lowerUnaryTerm @integerBitWidth @x @(SBV.SBV (SBV.IntN xn)) @a @(SBV.SBV (SBV.IntN an))
                  config
                  t
                  t1
                  ( if isSignedExt
                      then SBV.signExtend
                      else \x ->
                        SBV.sFromIntegral
                          (SBV.zeroExtend (SBV.sFromIntegral x :: SBV.SBV (SBV.WordN xn)) :: SBV.SBV (SBV.WordN an))
                  )
                  m
          _ -> Nothing
      _ -> Nothing
    extractBV :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    extractBV = case (R.typeRep @x, R.typeRep @a) of
      (UnsignedBVType (_ :: proxy xn), UnsignedBVType (_ :: proxy an)) ->
        case selectView @WordN @an @xn t of
          Just (SelectMatchResult (_ :: proxy1 ix) (t1 :: Term (WordN xn))) ->
            Just $
              ev @ix @an @xn $
                lowerUnaryTerm config t t1 (SBV.bvExtract (Proxy @(an + ix - 1)) (Proxy @ix)) m
          _ -> Nothing
      (SignedBVType (_ :: proxy xn), SignedBVType (_ :: proxy an)) ->
        case selectView @IntN @an @xn t of
          Just (SelectMatchResult (_ :: proxy1 ix) (t1 :: Term (IntN xn))) ->
            Just $
              ev @ix @an @xn $
                lowerUnaryTerm config t t1 (SBV.bvExtract (Proxy @(an + ix - 1)) (Proxy @ix)) m
          _ -> Nothing
      _ -> Nothing
      where
        ev ::
          forall ix w ow r.
          ( KnownNat ix,
            KnownNat w,
            KnownNat ow,
            ix + w <= ow,
            1 <= ow,
            1 <= w
          ) =>
          ( ( ((((w + ix) - 1) - ix) + 1) ~ w,
              KnownNat ((w + ix) - 1),
              (((w + ix) - 1) + 1) <= ow,
              ix <= ((w + ix) - 1)
            ) =>
            r
          ) ->
          r
        ev r =
          let withEquality :: forall x1 x2 x3. x1 :~: x2 -> (x1 ~ x2 => x3) -> x3
              withEquality Refl ret = ret
              wpixm1repr :: NatRepr (w + ix - 1) = NatRepr (natVal (Proxy @w) + natVal (Proxy @ix) - 1)
              wpixleqow :: LeqProof (w + ix) ow = unsafeCoerce (LeqProof :: LeqProof 0 0)
              wpixm1p1cancel :: (((w + ix) - 1) + 1) :~: (w + ix) = unsafeCoerce (LeqProof :: LeqProof 0 0)
              ev1 :: LeqProof ix ((w + ix) - 1) = unsafeCoerce (LeqProof :: LeqProof 0 0)
           in withKnownNat wpixm1repr $
                withLeqProof wpixleqow $
                  withEquality wpixm1p1cancel $
                    withEquality (unsafeAxiom :: ((((w + ix) - 1) - ix) + 1) :~: w) $
                      withLeqProof ev1 r
lowerSinglePrimImpl config@ResolvedConfig {} t@(BinaryTerm _ op (_ :: Term x) (_ :: Term y)) m =
  fromMaybe errorMsg $ asum [numType, numOrdCmp, bitsType, concatBV, integerType, funcApply]
  where
    errorMsg :: forall t1. t1
    errorMsg = translateBinaryError (show op) (R.typeRep @x) (R.typeRep @y) (R.typeRep @a)
    numOrdCmp :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    numOrdCmp = case (R.typeRep @a, (config, R.typeRep @x)) of
      (BoolType, ResolvedNumOrdType) -> case t of
        LTNumTerm (t1' :: Term x) t2' -> Just $ lowerBinaryTerm config t t1' t2' (SBV..<) m
        LENumTerm (t1' :: Term x) t2' -> Just $ lowerBinaryTerm config t t1' t2' (SBV..<=) m
        _ -> Nothing
      _ -> Nothing
    numType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    numType = case (config, R.typeRep @a) of
      ResolvedNumType ->
        case t of
          TimesNumTerm (t1' :: Term a) t2' -> Just $ lowerBinaryTerm config t t1' t2' (*) m
          _ -> Nothing
      _ -> Nothing
    integerType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    integerType = case (config, R.typeRep @a) of
      (ResolvedConfig {}, IntegerType) ->
        case t of
          DivITerm t1' t2' -> Just $ lowerBinaryTerm config t t1' t2' SBV.sDiv m
          ModITerm t1' t2' -> Just $ lowerBinaryTerm config t t1' t2' SBV.sMod m
          _ -> Nothing
      _ -> Nothing
    bitsType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    bitsType = case (config, R.typeRep @a) of
      ResolvedBitsType ->
        case t of
          AndBitsTerm (t1 :: Term a) t2 -> Just $ lowerBinaryTerm config t t1 t2 (.&.) m
          OrBitsTerm (t1 :: Term a) t2 -> Just $ lowerBinaryTerm config t t1 t2 (.|.) m
          XorBitsTerm (t1 :: Term a) t2 -> Just $ lowerBinaryTerm config t t1 t2 xor m
          _ -> Nothing
      _ -> Nothing
    funcApply :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    funcApply = case (config, R.typeRep @a) of
      ResolvedDeepType -> Just $
        case t of
          ApplyFTerm (t1' :: Term (y =-> a)) (t2' :: Term y) -> do
            (m1, l1) <- lowerSinglePrimCached config t1' m
            (m2, l2) <- lowerSinglePrimCached config t2' m1
            let g = l1 l2
            return (addBiMapIntermediate (SomeTerm t) (toDyn g) m2, g)
          ApplyGTerm (t1' :: Term (y --> a)) (t2' :: Term y) -> do
            (m1, l1) <- lowerSinglePrimCached config t1' m
            (m2, l2) <- lowerSinglePrimCached config t2' m1
            let g = l1 l2
            return (addBiMapIntermediate (SomeTerm t) (toDyn g) m2, g)
          _ -> errorMsg
      _ -> Nothing
    concatBV :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    concatBV = case (R.typeRep @x, R.typeRep @y, R.typeRep @a) of
      (UnsignedBVType (_ :: proxy xn), UnsignedBVType (_ :: proxy yn), UnsignedBVType (_ :: proxy an)) ->
        case concatView @WordN @xn @yn @an t of
          Just (ConcatMatchResult (t1 :: Term (WordN xn)) (t2 :: Term (WordN yn))) ->
            Just $ lowerBinaryTerm config t t1 t2 (SBV.#) m
          _ -> Nothing
      (SignedBVType (_ :: proxy xn), SignedBVType (_ :: proxy yn), SignedBVType (_ :: proxy an)) ->
        case concatView @IntN @xn @yn @an t of
          Just (ConcatMatchResult (t1 :: Term (IntN xn)) (t2 :: Term (IntN yn))) ->
            Just $
              lowerBinaryTerm
                config
                t
                t1
                t2
                ( \(x :: SBV.SInt xn) (y :: SBV.SInt yn) ->
                    SBV.sFromIntegral $
                      (SBV.sFromIntegral x :: SBV.SWord xn) SBV.# (SBV.sFromIntegral y :: SBV.SWord yn)
                )
                m
          _ -> Nothing
      _ -> Nothing
lowerSinglePrimImpl ResolvedConfig {} (TernaryTerm _ op (_ :: Term x) (_ :: Term y) (_ :: Term z)) _ = errorMsg
  where
    errorMsg :: forall t1. t1
    errorMsg = translateTernaryError (show op) (R.typeRep @x) (R.typeRep @y) (R.typeRep @z) (R.typeRep @a)
lowerSinglePrimImpl config t@(NotTerm _ arg) m = lowerUnaryTerm config t arg SBV.sNot m
lowerSinglePrimImpl config t@(OrTerm _ arg1 arg2) m = lowerBinaryTerm config t arg1 arg2 (SBV..||) m
lowerSinglePrimImpl config t@(AndTerm _ arg1 arg2) m = lowerBinaryTerm config t arg1 arg2 (SBV..&&) m
lowerSinglePrimImpl config t@(EqvTerm _ (arg1 :: Term x) arg2) m =
  case (config, R.typeRep @x) of
    ResolvedSimpleType -> lowerBinaryTerm config t arg1 arg2 (SBV..==) m
    _ -> translateBinaryError "(==)" (R.typeRep @x) (R.typeRep @x) (R.typeRep @a)
lowerSinglePrimImpl config t@(ITETerm _ cond arg1 arg2) m =
  case (config, R.typeRep @a) of
    ResolvedSimpleType -> do
      (m1, l1) <- lowerSinglePrimCached config cond m
      (m2, l2) <- lowerSinglePrimCached config arg1 m1
      (m3, l3) <- lowerSinglePrimCached config arg2 m2
      let g = SBV.ite l1 l2 l3
      return (addBiMapIntermediate (SomeTerm t) (toDyn g) m3, g)
    _ -> translateBinaryError "ite" (R.typeRep @Bool) (R.typeRep @a) (R.typeRep @a) (R.typeRep @a)
lowerSinglePrimImpl config t@(AddNumTerm _ arg1 arg2) m =
  case (config, R.typeRep @a) of
    ResolvedNumType -> lowerBinaryTerm config t arg1 arg2 (+) m
    _ -> translateBinaryError "(+)" (R.typeRep @a) (R.typeRep @a) (R.typeRep @a)
lowerSinglePrimImpl _ _ _ = error "Should never happen"

unsafeMkNatRepr :: Int -> NatRepr w
unsafeMkNatRepr x = NatRepr (fromInteger $ toInteger x)

unsafeWithNonZeroKnownNat :: forall w r. Int -> ((KnownNat w, 1 <= w) => r) -> r
unsafeWithNonZeroKnownNat i r
  | i <= 0 = error "Not an nonzero natural number"
  | otherwise = withKnownNat @w (unsafeMkNatRepr i) $ unsafeBVIsNonZero r
  where
    unsafeBVIsNonZero :: ((1 <= w) => r) -> r
    unsafeBVIsNonZero r1 = case unsafeAxiom :: w :~: 1 of
      Refl -> r1

bvIsNonZeroFromGEq1 :: forall w r. (1 <= w) => ((SBV.BVIsNonZero w) => r) -> r
bvIsNonZeroFromGEq1 r1 = case unsafeAxiom :: w :~: 1 of
  Refl -> r1

parseModel :: forall integerBitWidth. GrisetteSMTConfig integerBitWidth -> SBVI.SMTModel -> SymBiMap -> PM.Model
parseModel _ (SBVI.SMTModel _ _ assoc uifuncs) mp = foldr gouifuncs (foldr goassoc PM.empty assoc) uifuncs
  where
    goassoc :: (String, SBVI.CV) -> PM.Model -> PM.Model
    goassoc (name, cv) m = case findStringToSymbol name mp of
      Just s@(TermSymbol (_ :: R.TypeRep t) _) ->
        PM.insert m s (resolveSingle (R.typeRep @t) cv)
      Nothing -> error "Bad"
    resolveSingle :: R.TypeRep a -> SBVI.CV -> a
    resolveSingle t (SBVI.CV SBVI.KBool (SBVI.CInteger n)) =
      case R.eqTypeRep t (R.typeRep @Bool) of
        Just R.HRefl -> n /= 0
        Nothing -> error "Bad type"
    resolveSingle t (SBVI.CV SBVI.KUnbounded (SBVI.CInteger i)) =
      case R.eqTypeRep t (R.typeRep @Integer) of
        Just R.HRefl -> i
        Nothing -> error "Bad type"
    resolveSingle t (SBVI.CV (SBVI.KBounded _ bitWidth) (SBVI.CInteger i)) =
      case R.eqTypeRep t (R.typeRep @Integer) of
        Just R.HRefl -> i
        _ -> case t of
          R.App a (n :: R.TypeRep w) ->
            case R.eqTypeRep (R.typeRepKind n) (R.typeRep @Nat) of
              Just R.HRefl ->
                unsafeWithNonZeroKnownNat @w bitWidth $
                  case (R.eqTypeRep a (R.typeRep @IntN), R.eqTypeRep a (R.typeRep @WordN)) of
                    (Just R.HRefl, _) ->
                      fromInteger i
                    (_, Just R.HRefl) -> fromInteger i
                    _ -> error "Bad type"
              _ -> error "Bad type"
          _ -> error "Bad type"
    resolveSingle _ _ = error "Unknown cv"

    buildConstFunc :: (SupportedPrim a, SupportedPrim r) => R.TypeRep a -> R.TypeRep r -> SBVI.CV -> a =-> r
    buildConstFunc _ tr v = case tr of
      TFunType (ta2' :: R.TypeRep a2) (tr2' :: R.TypeRep r2) -> TabularFunc [] $ buildConstFunc ta2' tr2' v
      _ -> TabularFunc [] $ resolveSingle tr v

    goutfuncResolve ::
      forall a r.
      (SupportedPrim a, SupportedPrim r) =>
      R.TypeRep a ->
      R.TypeRep r ->
      ([([SBVI.CV], SBVI.CV)], SBVI.CV) ->
      (a =-> r)
    goutfuncResolve ta1 ta2 (l, s) =
      case ta2 of
        TFunType (ta2' :: R.TypeRep a2) (tr2' :: R.TypeRep r2) ->
          TabularFunc
            (second (\r -> goutfuncResolve ta2' tr2' (r, s)) <$> partition ta1 l)
            (buildConstFunc ta2' tr2' s)
        _ ->
          TabularFunc
            (bimap (resolveSingle ta1 . head) (resolveSingle ta2) <$> l)
            (resolveSingle ta2 s)

    gougfuncResolve ::
      forall a r.
      (SupportedPrim a, SupportedPrim r) =>
      Int ->
      R.TypeRep a ->
      R.TypeRep r ->
      ([([SBVI.CV], SBVI.CV)], SBVI.CV) ->
      (a --> r)
    gougfuncResolve idx ta1 ta2 (l, s) =
      case ta2 of
        GFunType (ta2' :: R.TypeRep a2) (tr2' :: R.TypeRep r2) ->
          let symb = WithInfo (IndexedSymbol "arg" idx) FuncArg
              funs = second (\r -> gougfuncResolve (idx + 1) ta2' tr2' (r, s)) <$> partition ta1 l
              def = gougfuncResolve (idx + 1) ta2' tr2' ([], s)
              body = foldl' (\acc (v, f) -> pevalITETerm (pevalEqvTerm (iinfosymbTerm "arg" idx FuncArg) (concTerm v)) (concTerm f) acc) (concTerm def) funs
           in GeneralFunc R.typeRep symb body
        _ ->
          let symb = WithInfo (IndexedSymbol "arg" idx) FuncArg
              vs = bimap (resolveSingle ta1 . head) (resolveSingle ta2) <$> l
              def = resolveSingle ta2 s
              body = foldl' (\acc (v, a) -> pevalITETerm (pevalEqvTerm (iinfosymbTerm "arg" idx FuncArg) (concTerm v)) (concTerm a) acc) (concTerm def) vs
           in GeneralFunc R.typeRep symb body
    partition :: R.TypeRep a -> [([SBVI.CV], SBVI.CV)] -> [(a, [([SBVI.CV], SBVI.CV)])]
    partition t = case (R.eqTypeRep t (R.typeRep @Bool), R.eqTypeRep t (R.typeRep @Integer)) of
      (Just R.HRefl, _) -> partitionWithOrd . resolveFirst t
      (_, Just R.HRefl) -> partitionWithOrd . resolveFirst t
      _ -> case t of
        R.App bv _ -> case (R.eqTypeRep bv (R.typeRep @IntN), R.eqTypeRep bv (R.typeRep @WordN)) of
          (Just R.HRefl, _) -> fmap (first IntN) . partitionWithOrd . fmap (first unIntN) . resolveFirst t
          (_, Just R.HRefl) -> partitionWithOrd . resolveFirst t
          _ -> error "Unknown type"
        _ -> error "Unknown type"

    resolveFirst :: R.TypeRep a -> [([SBVI.CV], SBVI.CV)] -> [(a, [([SBVI.CV], SBVI.CV)])]
    resolveFirst tf = fmap (\(x : xs, v) -> (resolveSingle tf x, [(xs, v)]))

    partitionWithOrd :: forall a. Ord a => [(a, [([SBVI.CV], SBVI.CV)])] -> [(a, [([SBVI.CV], SBVI.CV)])]
    partitionWithOrd v = go sorted
      where
        sorted = sortWith fst v
        go (x : x1 : xs) =
          if fst x == fst x1
            then go $ (fst x, snd x ++ snd x1) : xs
            else x : go (x1 : xs)
        go x = x

    gouifuncs :: (String, (SBVI.SBVType, ([([SBVI.CV], SBVI.CV)], SBVI.CV))) -> PM.Model -> PM.Model
    gouifuncs (name, (SBVI.SBVType _, l)) m = case findStringToSymbol name mp of
      Just s@(TermSymbol (_ :: R.TypeRep t) _) -> case R.typeRep @t of
        t@(TFunType a r) -> R.withTypeable t $ PM.insert m s $ goutfuncResolve a r l
        t@(GFunType a r) -> R.withTypeable t $ PM.insert m s $ gougfuncResolve 0 a r l
        _ -> error "Bad"
      Nothing -> error "Bad"

-- helpers

data BVTypeContainer bv k where
  BVTypeContainer :: (SBV.BVIsNonZero n, KnownNat n, 1 <= n, k ~ bv n) => Proxy n -> BVTypeContainer bv k

signedBVTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (BVTypeContainer IntN t)
signedBVTypeView t = case t of
  R.App s (n :: R.TypeRep w) ->
    case (R.eqTypeRep s (R.typeRep @IntN), R.eqTypeRep (R.typeRepKind n) (R.typeRep @Nat)) of
      (Just R.HRefl, Just R.HRefl) ->
        Just $ unsafeBVIsNonZero @w $ withPrim (Proxy @t) (BVTypeContainer Proxy)
      _ -> Nothing
  _ -> Nothing
  where
    unsafeBVIsNonZero :: forall w r. ((SBV.BVIsNonZero w) => r) -> r
    unsafeBVIsNonZero r1 = case unsafeAxiom :: w :~: 1 of
      Refl -> r1

pattern SignedBVType ::
  forall t.
  (SupportedPrim t) =>
  forall (n :: Nat).
  (t ~~ IntN n, KnownNat n, 1 <= n, SBV.BVIsNonZero n) =>
  Proxy n ->
  R.TypeRep t
pattern SignedBVType p <- (signedBVTypeView @t -> Just (BVTypeContainer p))

unsignedBVTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (BVTypeContainer WordN t)
unsignedBVTypeView t = case t of
  R.App s (n :: R.TypeRep w) ->
    case (R.eqTypeRep s (R.typeRep @WordN), R.eqTypeRep (R.typeRepKind n) (R.typeRep @Nat)) of
      (Just R.HRefl, Just R.HRefl) ->
        Just $ unsafeBVIsNonZero @w $ withPrim (Proxy @t) (BVTypeContainer Proxy)
      _ -> Nothing
  _ -> Nothing
  where
    unsafeBVIsNonZero :: forall w r. ((SBV.BVIsNonZero w) => r) -> r
    unsafeBVIsNonZero r1 = case unsafeAxiom :: w :~: 1 of
      Refl -> r1

pattern UnsignedBVType ::
  forall t.
  (SupportedPrim t) =>
  forall (n :: Nat).
  (t ~~ WordN n, KnownNat n, 1 <= n, SBV.BVIsNonZero n) =>
  Proxy n ->
  R.TypeRep t
pattern UnsignedBVType p <- (unsignedBVTypeView @t -> Just (BVTypeContainer p))

data TFunTypeContainer :: forall k. k -> Type where
  TFunTypeContainer :: (SupportedPrim a, SupportedPrim b) => R.TypeRep a -> R.TypeRep b -> TFunTypeContainer (a =-> b)

tFunTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (TFunTypeContainer t)
tFunTypeView t = case t of
  R.App (R.App arr (ta2' :: R.TypeRep a2)) (tr2' :: R.TypeRep r2) ->
    case R.eqTypeRep arr (R.typeRep @(=->)) of
      Just R.HRefl -> Just $ withPrim (Proxy @t) $ TFunTypeContainer ta2' tr2'
      Nothing -> Nothing
  _ -> Nothing

pattern TFunType ::
  forall t.
  (SupportedPrim t) =>
  forall (a :: Type) (b :: Type).
  (t ~~ (a =-> b), SupportedPrim a, SupportedPrim b) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep t
pattern TFunType a b <-
  (tFunTypeView -> Just (TFunTypeContainer a b))
  where
    TFunType a b = R.App (R.App (R.typeRep @(=->)) a) b

pattern TFun3Type ::
  forall t.
  (SupportedPrim t) =>
  forall (a :: Type) (b :: Type) (c :: Type).
  (t ~~ (a =-> b =-> c), SupportedPrim a, SupportedPrim b, SupportedPrim c) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep c ->
  R.TypeRep t
pattern TFun3Type a b c = TFunType a (TFunType b c)

data GFunTypeContainer :: forall k. k -> Type where
  GFunTypeContainer :: (SupportedPrim a, SupportedPrim b) => R.TypeRep a -> R.TypeRep b -> GFunTypeContainer (a --> b)

gFunTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (GFunTypeContainer t)
gFunTypeView t = case t of
  R.App (R.App arr (ta2' :: R.TypeRep a2)) (tr2' :: R.TypeRep r2) ->
    case R.eqTypeRep arr (R.typeRep @(-->)) of
      Just R.HRefl -> Just $ withPrim (Proxy @t) $ GFunTypeContainer ta2' tr2'
      Nothing -> Nothing
  _ -> Nothing

pattern GFunType ::
  forall t.
  (SupportedPrim t) =>
  forall (a :: Type) (b :: Type).
  (t ~~ (a --> b), SupportedPrim a, SupportedPrim b) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep t
pattern GFunType a b <-
  (gFunTypeView -> Just (GFunTypeContainer a b))
  where
    GFunType a b = R.App (R.App (R.typeRep @(-->)) a) b

pattern GFun3Type ::
  forall t.
  (SupportedPrim t) =>
  forall (a :: Type) (b :: Type) (c :: Type).
  (t ~~ (a --> b --> c), SupportedPrim a, SupportedPrim b, SupportedPrim c) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep c ->
  R.TypeRep t
pattern GFun3Type a b c = GFunType a (GFunType b c)

pattern BoolType ::
  forall t.
  () =>
  (t ~~ Bool) =>
  R.TypeRep t
pattern BoolType <- (R.eqTypeRep (R.typeRep @Bool) -> Just R.HRefl)

pattern IntegerType ::
  forall t.
  () =>
  (t ~~ Integer) =>
  R.TypeRep t
pattern IntegerType <- (R.eqTypeRep (R.typeRep @Integer) -> Just R.HRefl)

type ConfigConstraint integerBitWidth s =
  ( SBV.SBV s ~ TermTy integerBitWidth Integer,
    SBV.SymVal s,
    SBV.HasKind s,
    Typeable s,
    Num (SBV.SBV s),
    Num s,
    SBV.OrdSymbolic (SBV.SBV s),
    Ord s,
    SBV.SDivisible (SBV.SBV s),
    SBV.OrdSymbolic (SBV.SBV s),
    SBV.Mergeable (SBV.SBV s)
  )

data DictConfig integerBitWidth where
  DictConfig ::
    forall s integerBitWidth.
    (ConfigConstraint integerBitWidth s) =>
    SBV.SMTConfig ->
    DictConfig integerBitWidth

resolveConfigView ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  DictConfig integerBitWidth
resolveConfigView config = case config of
  UnboundedReasoning c -> DictConfig c
  BoundedReasoning c -> DictConfig c

pattern ResolvedConfig ::
  forall integerBitWidth.
  () =>
  forall s.
  ConfigConstraint integerBitWidth s =>
  SBV.SMTConfig ->
  GrisetteSMTConfig integerBitWidth
pattern ResolvedConfig c <- (resolveConfigView -> DictConfig c)

type SimpleTypeConstraint integerBitWidth s s' =
  ( SBV.SBV s' ~ TermTy integerBitWidth s,
    SBV.SymVal s',
    SBV.HasKind s',
    Typeable s',
    SBV.OrdSymbolic (SBV.SBV s'),
    SBV.Mergeable (SBV.SBV s')
  )

type TypeResolver dictType =
  forall integerBitWidth s.
  (SupportedPrim s) =>
  (GrisetteSMTConfig integerBitWidth, R.TypeRep s) ->
  Maybe (dictType integerBitWidth s)

-- has to declare this because GHC does not support impredicative polymorphism
data DictSimpleType integerBitWidth s where
  DictSimpleType ::
    forall integerBitWidth s s'.
    (SimpleTypeConstraint integerBitWidth s s') =>
    DictSimpleType integerBitWidth s

resolveSimpleTypeView :: TypeResolver DictSimpleType
resolveSimpleTypeView (ResolvedConfig {}, s) = case s of
  BoolType -> Just DictSimpleType
  IntegerType -> Just DictSimpleType
  SignedBVType _ -> Just DictSimpleType
  UnsignedBVType _ -> Just DictSimpleType
  _ -> Nothing
resolveSimpleTypeView _ = error "Should never happen, make compiler happy"

pattern ResolvedSimpleType ::
  forall integerBitWidth s.
  (SupportedPrim s) =>
  forall s'.
  SimpleTypeConstraint integerBitWidth s s' =>
  (GrisetteSMTConfig integerBitWidth, R.TypeRep s)
pattern ResolvedSimpleType <- (resolveSimpleTypeView -> Just DictSimpleType)

type DeepTypeConstraint integerBitWidth s s' =
  ( s' ~ TermTy integerBitWidth s,
    Typeable s',
    SBV.Mergeable s'
  )

data DictDeepType integerBitWidth s where
  DictDeepType ::
    forall integerBitWidth s s'.
    (DeepTypeConstraint integerBitWidth s s') =>
    DictDeepType integerBitWidth s

resolveDeepTypeView :: TypeResolver DictDeepType
resolveDeepTypeView r = case r of
  ResolvedSimpleType -> Just DictDeepType
  (config, TFunType (ta :: R.TypeRep a) (tb :: R.TypeRep b)) ->
    case (resolveDeepTypeView (config, ta), resolveDeepTypeView (config, tb)) of
      (Just DictDeepType, Just DictDeepType) -> Just DictDeepType
      _ -> Nothing
  (config, GFunType (ta :: R.TypeRep a) (tb :: R.TypeRep b)) ->
    case (resolveDeepTypeView (config, ta), resolveDeepTypeView (config, tb)) of
      (Just DictDeepType, Just DictDeepType) -> Just DictDeepType
      _ -> Nothing
  _ -> Nothing

pattern ResolvedDeepType ::
  forall integerBitWidth s.
  (SupportedPrim s) =>
  forall s'.
  DeepTypeConstraint integerBitWidth s s' =>
  (GrisetteSMTConfig integerBitWidth, R.TypeRep s)
pattern ResolvedDeepType <- (resolveDeepTypeView -> Just DictDeepType)

type NumTypeConstraint integerBitWidth s s' =
  ( SimpleTypeConstraint integerBitWidth s s',
    Num (SBV.SBV s'),
    Num s',
    Num s
  )

data DictNumType integerBitWidth s where
  DictNumType ::
    forall integerBitWidth s s'.
    (NumTypeConstraint integerBitWidth s s') =>
    DictNumType integerBitWidth s

resolveNumTypeView :: TypeResolver DictNumType
resolveNumTypeView (ResolvedConfig {}, s) = case s of
  IntegerType -> Just DictNumType
  SignedBVType _ -> Just DictNumType
  UnsignedBVType _ -> Just DictNumType
  _ -> Nothing
resolveNumTypeView _ = error "Should never happen, make compiler happy"

pattern ResolvedNumType ::
  forall integerBitWidth s.
  (SupportedPrim s) =>
  forall s'.
  NumTypeConstraint integerBitWidth s s' =>
  (GrisetteSMTConfig integerBitWidth, R.TypeRep s)
pattern ResolvedNumType <- (resolveNumTypeView -> Just DictNumType)

type NumOrdTypeConstraint integerBitWidth s s' =
  ( NumTypeConstraint integerBitWidth s s',
    SBV.OrdSymbolic (SBV.SBV s'),
    Ord s',
    Ord s
  )

data DictNumOrdType integerBitWidth s where
  DictNumOrdType ::
    forall integerBitWidth s s'.
    (NumOrdTypeConstraint integerBitWidth s s') =>
    DictNumOrdType integerBitWidth s

resolveNumOrdTypeView :: TypeResolver DictNumOrdType
resolveNumOrdTypeView (ResolvedConfig {}, s) = case s of
  IntegerType -> Just DictNumOrdType
  SignedBVType _ -> Just DictNumOrdType
  UnsignedBVType _ -> Just DictNumOrdType
  _ -> Nothing
resolveNumOrdTypeView _ = error "Should never happen, make compiler happy"

pattern ResolvedNumOrdType ::
  forall integerBitWidth s.
  (SupportedPrim s) =>
  forall s'.
  NumOrdTypeConstraint integerBitWidth s s' =>
  (GrisetteSMTConfig integerBitWidth, R.TypeRep s)
pattern ResolvedNumOrdType <- (resolveNumOrdTypeView -> Just DictNumOrdType)

type BitsTypeConstraint integerBitWidth s s' =
  ( SimpleTypeConstraint integerBitWidth s s',
    Bits (SBV.SBV s'),
    Bits s',
    Bits s
  )

data DictBitsType integerBitWidth s where
  DictBitsType ::
    forall integerBitWidth s s'.
    (BitsTypeConstraint integerBitWidth s s') =>
    DictBitsType integerBitWidth s

resolveBitsTypeView :: TypeResolver DictBitsType
resolveBitsTypeView (ResolvedConfig {}, s) = case s of
  SignedBVType _ -> Just DictBitsType
  UnsignedBVType _ -> Just DictBitsType
  _ -> Nothing
resolveBitsTypeView _ = error "Should never happen, make compiler happy"

pattern ResolvedBitsType ::
  forall integerBitWidth s.
  (SupportedPrim s) =>
  forall s'.
  BitsTypeConstraint integerBitWidth s s' =>
  (GrisetteSMTConfig integerBitWidth, R.TypeRep s)
pattern ResolvedBitsType <- (resolveBitsTypeView -> Just DictBitsType)
