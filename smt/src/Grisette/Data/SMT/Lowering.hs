{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.SMT.Lowering
  ( lowerSinglePrim,
    parseModel,
  )
where

import Data.Bifunctor
import qualified Data.BitVector.Sized as BV
import qualified Data.BitVector.Sized.Signed as BVS
import qualified Data.BitVector.Sized.Unsigned as BVU
import Data.Dynamic
import Data.Foldable
import qualified Data.HashMap.Strict as M
import Data.Maybe (fromMaybe)
import Data.Parameterized.Axiom (unsafeAxiom)
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import qualified Data.SBV as SBV
import qualified Data.SBV.Internals as SBVI
import Data.Type.Equality (type (~~))
import Data.Typeable
import GHC.Exts (sortWith)
import GHC.TypeNats
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as PM
import Grisette.Data.Prim.Num
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.SMT.Config
import Grisette.Data.TabularFunc
import qualified Type.Reflection as R
import Unsafe.Coerce

data SymBiMap = SymBiMap
  { biMapToSBV :: M.HashMap SomeTerm Dynamic,
    biMapFromSBV :: M.HashMap String TermSymbol
  }
  deriving (Show)

addBiMap :: SomeTerm -> Dynamic -> String -> TermSymbol -> SymBiMap -> SymBiMap
addBiMap s d n sb (SymBiMap t f) = SymBiMap (M.insert s d t) (M.insert n sb f)

addBiMapIntermediate :: SomeTerm -> Dynamic -> SymBiMap -> SymBiMap
addBiMapIntermediate s d (SymBiMap t f) = SymBiMap (M.insert s d t) f

findStringToSymbol :: String -> SymBiMap -> Maybe TermSymbol
findStringToSymbol s (SymBiMap _ f) = M.lookup s f

buildUFunc11 ::
  forall integerBitWidth s1 s2 a.
  (SupportedPrim a, SupportedPrim s1, SupportedPrim s2) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 =-> s2)))
buildUFunc11 config ta tb term@(SymbTerm _ ts) m = case ((config, ta), (config, tb)) of
  (ResolvedSimpleType, ResolvedSimpleType) ->
    let name = "ufunc_" ++ show ts
        f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2) name
     in Just $ return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
  _ -> Nothing
buildUFunc11 _ _ _ _ _ = error "Should only be called on SymbTerm"

buildUFunc111 ::
  forall integerBitWidth s1 s2 s3 a.
  (SupportedPrim a, SupportedPrim s1, SupportedPrim s2, SupportedPrim s3) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  R.TypeRep s3 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 =-> s2 =-> s3)))
buildUFunc111 config ta tb tc term@(SymbTerm _ ts) m = case ((config, ta), (config, tb), (config, tc)) of
  (ResolvedSimpleType, ResolvedSimpleType, ResolvedSimpleType) ->
    let name = "ufunc_" ++ show ts
        f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2 -> TermTy integerBitWidth s3) name
     in Just $ return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
  _ -> Nothing
buildUFunc111 _ _ _ _ _ _ = error "Should only be called on SymbTerm"

lowerSinglePrimUFunc ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
lowerSinglePrimUFunc config t@(SymbTerm _ _) m =
  case R.typeRep @a of
    TFun3Type (t1 :: R.TypeRep a1) (t2 :: R.TypeRep a2) (t3 :: R.TypeRep a3) -> buildUFunc111 config t1 t2 t3 t m
    TFunType (ta :: R.TypeRep b) (tb :: R.TypeRep b1) -> buildUFunc11 config ta tb t m
    _ -> Nothing
lowerSinglePrimUFunc _ _ _ = error "Should not call this function"

lowerUnaryTerm ::
  forall integerBitWidth a a1 x x1.
  (Typeable x1, a1 ~ TermTy integerBitWidth a, SupportedPrim x) =>
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
  (Typeable x1, a1 ~ TermTy integerBitWidth a, b1 ~ TermTy integerBitWidth b, SupportedPrim x) =>
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
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)
lowerSinglePrimCached config t m =
  introSupportedPrimConstraint t $
    case (config, R.typeRep @a) of
      ResolvedDeepType ->
        case M.lookup (SomeTerm t) (biMapToSBV m) of
          Just x -> return (m, fromDyn x undefined)
          Nothing -> lowerSinglePrimImpl config t m
      _ -> error $ "Don't know how to translate the type " ++ show (typeRep (Proxy @a)) ++ " to SMT"

lowerSinglePrim ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)
lowerSinglePrim config t = lowerSinglePrimCached config t (SymBiMap M.empty M.empty)

lowerSinglePrimImpl ::
  forall integerBitWidth a.
  GrisetteSMTConfig integerBitWidth ->
  Term a ->
  SymBiMap ->
  SBV.Symbolic (SymBiMap, TermTy integerBitWidth a)
lowerSinglePrimImpl ResolvedConfig {} (ConcTerm _ v) m =
  case R.typeRep @a of
    BoolType -> return (m, if v then SBV.sTrue else SBV.sFalse)
    IntegerType -> return (m, fromInteger v)
    SignedBVType _ -> case v of
      BVS.SignedBV (BV.BV x) -> return (m, fromInteger x)
    UnsignedBVType _ -> case v of
      BVU.UnsignedBV (BV.BV x) -> return (m, fromInteger x)
    _ -> error $ "Don't know how to translate the type " ++ show (typeRep (Proxy @a)) ++ " to SMT"
lowerSinglePrimImpl config t@(SymbTerm _ ts) m =
  fromMaybe errorMsg $ asum [simple, ufunc]
  where
    errorMsg :: forall x. x
    errorMsg = error $ "Don't know how to translate the type " ++ show (typeRep (Proxy @a)) ++ " to SMT"
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
  fromMaybe errorMsg $ asum [numType, boolType {-, integerType-}]
  where
    errorMsg :: forall t1. t1
    errorMsg =
      error $
        "Don't know how to translate the op " ++ show op ++ " :: "
          ++ show (R.typeRep @x)
          ++ " -> "
          ++ show (R.typeRep @a)
    numType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    numType = case (config, R.typeRep @a) of
      ResolvedNumType ->
        case t of
          UMinusNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 (\x -> - x) m
          SignumNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 signum m
          AbsNumTerm (t1 :: Term a) -> Just $ lowerUnaryTerm config t t1 abs m
          _ -> Nothing
      _ -> Nothing
    boolType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    boolType = case R.typeRep @a of
      BoolType -> case t of
        NotTerm t1 -> Just $ lowerUnaryTerm config t t1 SBV.sNot m
        _ -> Nothing
      _ -> Nothing
lowerSinglePrimImpl config@ResolvedConfig {} t@(BinaryTerm _ op (_ :: Term x) (_ :: Term y)) m =
  fromMaybe errorMsg $ asum [numType, numOrdCmp, simpleBoolType, eqTerm, funcApply]
  where
    errorMsg :: forall t1. t1
    errorMsg =
      error $
        "Don't know how to translate the op " ++ show op ++ " :: "
          ++ show (R.typeRep @x)
          ++ " -> "
          ++ show (R.typeRep @y)
          ++ " -> "
          ++ show (R.typeRep @a)
    eqTerm :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    eqTerm = case ((config, R.typeRep @x), R.typeRep @a) of
      (ResolvedSimpleType, BoolType) -> case t of
        EqvTerm (t1' :: Term x) t2' -> Just $ lowerBinaryTerm config t t1' t2' (SBV..==) m
        _ -> Nothing
      _ -> Nothing
    simpleBoolType :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    simpleBoolType = case R.typeRep @a of
      BoolType -> case t of
        AndTerm t1' t2' -> Just $ lowerBinaryTerm config t t1' t2' (SBV..&&) m
        OrTerm t1' t2' -> Just $ lowerBinaryTerm config t t1' t2' (SBV..||) m
        _ -> Nothing
      _ -> Nothing
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
          AddNumTerm (t1' :: Term a) t2' -> Just $ lowerBinaryTerm config t t1' t2' (+) m
          TimesNumTerm (t1' :: Term a) t2' -> Just $ lowerBinaryTerm config t t1' t2' (*) m
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
          _ -> errorMsg
      _ -> Nothing
lowerSinglePrimImpl config@ResolvedConfig {} t@(TernaryTerm _ op (_ :: Term x) (_ :: Term y) (_ :: Term z)) m =
  case (config, R.typeRep @a) of
    ResolvedDeepType ->
      case t of
        ITETerm c t1 f1 -> do
          (m1, l1) <- lowerSinglePrimCached config c m
          (m2, l2) <- lowerSinglePrimCached config t1 m1
          (m3, l3) <- lowerSinglePrimCached config f1 m2
          let g = SBV.ite l1 l2 l3
          return (addBiMapIntermediate (SomeTerm t) (toDyn g) m3, g)
        _ -> errorMsg
    _ -> errorMsg
  where
    errorMsg :: forall t1. t1
    errorMsg =
      error $
        "Don't know how to translate the op " ++ show op ++ " :: "
          ++ show (R.typeRep @x)
          ++ " -> "
          ++ show (R.typeRep @y)
          ++ " -> "
          ++ show (R.typeRep @z)
          ++ " -> "
          ++ show (R.typeRep @a)
lowerSinglePrimImpl _ _ _ = error "Should never happen"

unsafeMkNatRepr :: Int -> NatRepr w
unsafeMkNatRepr x =
  case mkNatRepr (fromInteger $ toInteger x) of
    Some v -> unsafeCoerce v

unsafeWithNonZeroKnownNat :: forall w r. Int -> ((KnownNat w, SBV.BVIsNonZero w) => r) -> r
unsafeWithNonZeroKnownNat i r
  | i <= 0 = error "Not an nonzero natural number"
  | otherwise = withKnownNat @w (unsafeMkNatRepr i) $ unsafeBVIsNonZero r
  where
    unsafeBVIsNonZero :: ((SBV.BVIsNonZero w) => r) -> r
    unsafeBVIsNonZero r1 = case unsafeAxiom :: w :~: 1 of
      Refl -> r1

parseModel :: forall integerBitWidth. GrisetteSMTConfig integerBitWidth -> SBVI.SMTModel -> SymBiMap -> PM.Model
parseModel _ (SBVI.SMTModel _ _ assoc uifuncs) mp = foldr gouifuncs (foldr goassoc PM.empty assoc) uifuncs
  where
    goassoc :: (String, SBVI.CV) -> PM.Model -> PM.Model
    goassoc (name, cv) m = case findStringToSymbol name mp of
      Just s@(TermSymbol (_ :: Proxy t) _) ->
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
                  case (R.eqTypeRep a (R.typeRep @BVS.SignedBV), R.eqTypeRep a (R.typeRep @BVU.UnsignedBV)) of
                    (Just R.HRefl, _) -> BVS.mkSignedBV knownNat i
                    (_, Just R.HRefl) -> BVU.mkUnsignedBV knownNat i
                    _ -> error "Bad type"
              _ -> error "Bad type"
          _ -> error "Bad type"
    resolveSingle _ _ = error "Unknown cv"

    buildConstFunc :: (SupportedPrim a, SupportedPrim r) => R.TypeRep a -> R.TypeRep r -> SBVI.CV -> a =-> r
    buildConstFunc _ tr v = case tr of
      TFunType (ta2' :: R.TypeRep a2) (tr2' :: R.TypeRep r2) -> TabularFunc [] $ buildConstFunc ta2' tr2' v
      _ -> TabularFunc [] $ resolveSingle tr v

    goufuncResolve ::
      forall a r.
      (SupportedPrim a, SupportedPrim r) =>
      R.TypeRep a ->
      R.TypeRep r ->
      ([([SBVI.CV], SBVI.CV)], SBVI.CV) ->
      (a =-> r)
    goufuncResolve ta1 ta2 (l, s) =
      case ta2 of
        TFunType (ta2' :: R.TypeRep a2) (tr2' :: R.TypeRep r2) ->
          TabularFunc
            (second (\r -> goufuncResolve ta2' tr2' (r, s)) <$> partition ta1 l)
            (buildConstFunc ta2' tr2' s)
        _ ->
          TabularFunc
            (bimap (resolveSingle ta1 . head) (resolveSingle ta2) <$> l)
            (resolveSingle ta2 s)

    partition :: R.TypeRep a -> [([SBVI.CV], SBVI.CV)] -> [(a, [([SBVI.CV], SBVI.CV)])]
    partition t = case (R.eqTypeRep t (R.typeRep @Bool), R.eqTypeRep t (R.typeRep @Integer)) of
      (Just R.HRefl, _) -> partitionWithOrd . resolveFirst t
      (_, Just R.HRefl) -> partitionWithOrd . resolveFirst t
      _ -> case t of
        R.App bv _ -> case (R.eqTypeRep bv (R.typeRep @BVS.SignedBV), R.eqTypeRep bv (R.typeRep @BVU.UnsignedBV)) of
          (Just R.HRefl, _) -> fmap (first BVS.SignedBV) . partitionWithOrd . fmap (first BVS.asBV) . resolveFirst t
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
      Just s@(TermSymbol (_ :: Proxy t) _) -> case R.typeRep @t of
        t@(TFunType a r) -> R.withTypeable t $ PM.insert m s $ goufuncResolve a r l
        _ -> error "Bad"
      Nothing -> error "Bad"

-- helpers

data SignedBVTypeContainer :: forall k. k -> * where
  SignedBVTypeContainer :: (SBV.BVIsNonZero n, KnownNat n, 1 <= n) => Proxy n -> SignedBVTypeContainer (BVS.SignedBV n)

signedBVTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (SignedBVTypeContainer t)
signedBVTypeView t = case t of
  R.App s (n :: R.TypeRep w) ->
    case (R.eqTypeRep s (R.typeRep @BVS.SignedBV), R.eqTypeRep (R.typeRepKind n) (R.typeRep @Nat)) of
      (Just R.HRefl, Just R.HRefl) ->
        Just $ unsafeBVIsNonZero @w $ withPrim @t (SignedBVTypeContainer Proxy)
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
  (t ~~ BVS.SignedBV n, KnownNat n, 1 <= n, SBV.BVIsNonZero n) =>
  Proxy n ->
  R.TypeRep t
pattern SignedBVType p <- (signedBVTypeView @t -> Just (SignedBVTypeContainer p))

data UnsignedBVTypeContainer :: forall k. k -> * where
  UnsignedBVTypeContainer :: (SBV.BVIsNonZero n, KnownNat n, 1 <= n) => Proxy n -> UnsignedBVTypeContainer (BVU.UnsignedBV n)

unsignedBVTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (UnsignedBVTypeContainer t)
unsignedBVTypeView t = case t of
  R.App s (n :: R.TypeRep w) ->
    case (R.eqTypeRep s (R.typeRep @BVU.UnsignedBV), R.eqTypeRep (R.typeRepKind n) (R.typeRep @Nat)) of
      (Just R.HRefl, Just R.HRefl) ->
        Just $ unsafeBVIsNonZero @w $ withPrim @t (UnsignedBVTypeContainer Proxy)
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
  (t ~~ BVU.UnsignedBV n, KnownNat n, 1 <= n, SBV.BVIsNonZero n) =>
  Proxy n ->
  R.TypeRep t
pattern UnsignedBVType p <- (unsignedBVTypeView @t -> Just (UnsignedBVTypeContainer p))

data TFunTypeContainer :: forall k. k -> * where
  TFunTypeContainer :: (SupportedPrim a, SupportedPrim b) => R.TypeRep a -> R.TypeRep b -> TFunTypeContainer (a =-> b)

tFunTypeView :: forall t. (SupportedPrim t) => R.TypeRep t -> Maybe (TFunTypeContainer t)
tFunTypeView t = case t of
  R.App (R.App arr (ta2' :: R.TypeRep a2)) (tr2' :: R.TypeRep r2) ->
    case R.eqTypeRep arr (R.typeRep @(=->)) of
      Just R.HRefl -> Just $ withPrim @t $ TFunTypeContainer ta2' tr2'
      Nothing -> Nothing
  _ -> Nothing

pattern TFunType ::
  forall t.
  (SupportedPrim t) =>
  forall (a :: *) (b :: *).
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
  forall (a :: *) (b :: *) (c :: *).
  (t ~~ (a =-> b =-> c), SupportedPrim a, SupportedPrim b, SupportedPrim c) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep c ->
  R.TypeRep t
pattern TFun3Type a b c = TFunType a (TFunType b c)

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