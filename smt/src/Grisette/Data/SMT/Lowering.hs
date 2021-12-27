{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import Control.Monad
import Data.Bifunctor
import Data.BitVector.Sized.Signed as BVS
import Data.BitVector.Sized.Unsigned as BVU
import Data.Dynamic
import qualified Data.HashMap.Strict as M
import Data.Maybe
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import qualified Data.SBV as SBV
import qualified Data.SBV.Internals as SBVI
import Data.Type.Equality (type (~~))
import Data.Typeable
import GHC.Exts (sortWith)
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.Num
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as PM
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.SMT.Config
import Grisette.Data.TabularFunc
import qualified Type.Reflection as R
import Unsafe.Coerce
import GHC.TypeNats
import Data.Parameterized.Axiom (unsafeAxiom)

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

resolveConfig ::
  forall integerBitWidth r.
  GrisetteSMTConfig integerBitWidth ->
  ( forall s1'.
    ( SBV.SBV s1' ~ TermTy integerBitWidth Integer,
      SBV.SymVal s1',
      SBV.HasKind s1',
      Typeable s1',
      Num (SBV.SBV s1'),
      SBV.SDivisible (SBV.SBV s1'),
      SBV.OrdSymbolic (SBV.SBV s1'),
      SBV.Mergeable (SBV.SBV s1')
    ) =>
    r
  ) ->
  r
resolveConfig config a = case config of
  UnboundedReasoning {} -> a
  BoundedReasoning {} -> a

resolveSimpleType ::
  forall s1 integerBitWidth r.
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  ( forall s1'.
    ( SBV.SBV s1' ~ TermTy integerBitWidth s1,
      SBV.SymVal s1',
      SBV.HasKind s1',
      Typeable s1',
      SBV.OrdSymbolic (SBV.SBV s1'),
      SBV.Mergeable (SBV.SBV s1')
    ) =>
    r
  ) ->
  Maybe r
resolveSimpleType config t a = R.withTypeable t $
  case (eqT @s1 @Bool, eqT @s1 @Integer) of
    (Just Refl, _) -> Just a
    (_, Just Refl) -> Just $ resolveConfig config a
    _ -> Nothing

resolveDeepType ::
  forall s1 integerBitWidth r.
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  ( forall s1'.
    ( s1' ~ TermTy integerBitWidth s1,
      Typeable s1',
      SBV.Mergeable s1'
    ) =>
    r
  ) ->
  Maybe r
resolveDeepType config t a =
  case (resolveSimpleType config t a, t) of
    (Just r, _) -> Just r
    (_, TFunType (ta :: R.TypeRep a) (tb :: R.TypeRep b)) -> join $ resolveDeepType config ta $ resolveDeepType config tb a
    _ -> Nothing

buildUFunc11 ::
  forall integerBitWidth s1 s2 a.
  (SupportedPrim a) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 =-> s2)))
buildUFunc11 config ta tb term@(SymbTerm _ ts@(TermSymbol s _)) m =
  join $
    resolveSimpleType @s1 config ta $
      resolveSimpleType @s2 config tb $
        let name = "ufunc_" ++ show s
            f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2) name
         in return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
buildUFunc11 _ _ _ _ _ = error "Should only be called on SymbTerm"

buildUFunc111 ::
  forall integerBitWidth s1 s2 s3 a.
  (SupportedPrim a) =>
  GrisetteSMTConfig integerBitWidth ->
  R.TypeRep s1 ->
  R.TypeRep s2 ->
  R.TypeRep s3 ->
  Term a ->
  SymBiMap ->
  Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth (s1 =-> s2 =-> s3)))
buildUFunc111 config ta tb tc term@(SymbTerm _ ts@(TermSymbol s _)) m =
  (join . join) $
    resolveSimpleType @s1 config ta $
      resolveSimpleType @s2 config tb $
        resolveSimpleType @s3 config tc $
          let name = "ufunc_" ++ show s
              f = SBV.uninterpret @(TermTy integerBitWidth s1 -> TermTy integerBitWidth s2 -> TermTy integerBitWidth s3) name
           in return (addBiMap (SomeTerm term) (toDyn f) name ts m, f)
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
    fromMaybe (error $ "Don't know how to translate the type " ++ show (typeRep (Proxy @a)) ++ " to SMT") $
      resolveDeepType @a @integerBitWidth @(SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
        config
        (R.typeRep @a)
        ( case M.lookup (SomeTerm t) (biMapToSBV m) of
            Just x -> return (m, fromDyn x undefined)
            Nothing -> lowerSinglePrimImpl config t m
        )

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
lowerSinglePrimImpl config (ConcTerm _ v) m =
  case (eqT @a @Bool, eqT @a @Integer) of
    (Just Refl, _) -> return (m, if v then SBV.sTrue else SBV.sFalse)
    (_, Just Refl) -> resolveConfig config $ return (m, fromInteger v)
    _ -> error $ "Don't know how to translate the type " ++ show (typeRep (Proxy @a)) ++ " to SMT"
lowerSinglePrimImpl config t@(SymbTerm _ ts@(TermSymbol s _)) m =
  fromMaybe errorMsg $
    resolveDeepType
      config
      (R.typeRep @a)
      ( case b1 of
          Just v -> v
          _ -> fromMaybe errorMsg (lowerSinglePrimUFunc config t m)
      )
  where
    errorMsg :: forall x. x
    errorMsg = error $ "Don't know how to translate the type " ++ show (typeRep (Proxy @a)) ++ " to SMT"
    b1 :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
    b1 = resolveSimpleType @a config (R.typeRep @a) $ do
      let name = show s
      (g :: TermTy integerBitWidth a) <- SBV.free name
      return (addBiMap (SomeTerm t) (toDyn g) name ts m, g)
lowerSinglePrimImpl config t@(UnaryTerm _ op (_ :: Term x)) m =
  resolveConfig config $
    case (eqT @a @Bool, eqT @a @Integer) of
      (Just Refl, _) -> do
        case t of
          NotTerm t1 -> lowerUnaryTerm config t t1 SBV.sNot m
          _ -> errorMsg
      (_, Just Refl) ->
        case t of
          UMinusITerm t1 -> lowerUnaryTerm config t t1 (\x -> - x) m
          SignumITerm t1 -> lowerUnaryTerm config t t1 signum m
          AbsITerm t1 -> lowerUnaryTerm config t t1 abs m
          UMinusNumTerm (t1 :: Term Integer) -> lowerUnaryTerm config t t1 (\x -> - x) m
          SignumNumTerm (t1 :: Term Integer) -> lowerUnaryTerm config t t1 signum m
          AbsNumTerm (t1 :: Term Integer) -> lowerUnaryTerm config t t1 abs m
          _ -> errorMsg
      _ -> errorMsg
  where
    errorMsg :: forall t1. t1
    errorMsg =
      error $
        "Don't know how to translate the op " ++ show op ++ " :: "
          ++ show (R.typeRep @x)
          ++ " -> "
          ++ show (R.typeRep @a)
lowerSinglePrimImpl config t@(BinaryTerm _ op (t1 :: Term x) (t2 :: Term y)) m =
  resolveConfig config $
    let s :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
        s =
          resolveSimpleType @x @integerBitWidth
            config
            (introSupportedPrimConstraint @x t1 R.typeRep)
            ( case (eqT @a @Bool, eqT @a @Integer) of
                (Just Refl, _) ->
                  ( case t of
                      EqvTerm (t1' :: Term x) t2' -> lowerBinaryTerm config t t1' t2' (SBV..==) m
                      AndTerm t1' t2' -> lowerBinaryTerm config t t1' t2' (SBV..&&) m
                      OrTerm t1' t2' -> lowerBinaryTerm config t t1' t2' (SBV..||) m
                      LTITerm t1' t2' -> lowerBinaryTerm config t t1' t2' (SBV..<) m
                      LEITerm t1' t2' -> lowerBinaryTerm config t t1' t2' (SBV..<=) m
                      _ -> errorMsg
                  )
                (_, Just Refl) ->
                  ( case t of
                      AddITerm t1' t2' -> lowerBinaryTerm config t t1' t2' (+) m
                      AddNumTerm (t1' :: Term Integer) t2' -> lowerBinaryTerm config t t1' t2' (+) m
                      TimesITerm t1' t2' -> lowerBinaryTerm config t t1' t2' (*) m
                      TimesNumTerm (t1' :: Term Integer) t2' -> lowerBinaryTerm config t t1' t2' (*) m
                      DivITerm t1' t2' -> lowerBinaryTerm config t t1' t2' SBV.sDiv m
                      _ -> errorMsg
                  )
                _ -> errorMsg
            )
        d :: Maybe (SBV.Symbolic (SymBiMap, TermTy integerBitWidth a))
        d =
          ( introSupportedPrimConstraint @y t2 $
              resolveDeepType @a @integerBitWidth
                config
                R.typeRep
                ( introSupportedPrimConstraint @y t2 $ case t of
                    ApplyFTerm (t1' :: Term (y =-> a)) (t2' :: Term y) -> do
                      (m1, l1) <- lowerSinglePrimCached config t1' m
                      (m2, l2) <- lowerSinglePrimCached config t2' m1
                      let g = l1 l2
                      return (addBiMapIntermediate (SomeTerm t) (toDyn g) m2, g)
                    _ -> errorMsg
                )
          )
     in case (s, d) of
          (Just r, _) -> r
          (_, Just r) -> r
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
          ++ show (R.typeRep @a)
lowerSinglePrimImpl config t@(TernaryTerm _ op (_ :: Term x) (t2 :: Term y) (_ :: Term z)) m =
  resolveConfig config $
    fromMaybe errorMsg $
      resolveDeepType @a @integerBitWidth
        config
        (introSupportedPrimConstraint @y t2 R.typeRep)
        ( case t of
            ITETerm c t1 f1 -> do
              (m1, l1) <- lowerSinglePrimCached config c m
              (m2, l2) <- lowerSinglePrimCached config t1 m1
              (m3, l3) <- lowerSinglePrimCached config f1 m2
              let g = SBV.ite l1 l2 l3
              return (addBiMapIntermediate (SomeTerm t) (toDyn g) m3, g)
            _ -> errorMsg
        )
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
      Just s -> case termSymbolTypeRep s of
        SomeTypeRepK1 (t :: R.TypeRep a) ->
          R.withTypeable t $ PM.insert m s (resolveSingle t cv)
        _ -> error "Assoc can only work for kind *"
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
                case (R.eqTypeRep a (R.typeRep @SignedBV), R.eqTypeRep a (R.typeRep @UnsignedBV)) of
                  (Just R.HRefl, _) -> mkSignedBV knownNat i
                  (_, Just R.HRefl) -> mkUnsignedBV knownNat i
                  _ -> error "Bad type"
              _ -> error "Bad type"
          _ -> error "Bad type"
    resolveSingle _ _ = error "Unknown cv"

    buildConstFunc :: R.TypeRep a -> R.TypeRep r -> SBVI.CV -> a =-> r
    buildConstFunc _ tr v = case tr of
      TFunType (ta2' :: R.TypeRep a2) (tr2' :: R.TypeRep r2) -> TabularFunc [] $ buildConstFunc ta2' tr2' v
      _ -> TabularFunc [] $ resolveSingle tr v

    goufuncResolve :: forall a r. R.TypeRep a -> R.TypeRep r -> ([([SBVI.CV], SBVI.CV)], SBVI.CV) -> (a =-> r)
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
        R.App bv _ -> case (R.eqTypeRep bv (R.typeRep @SignedBV), R.eqTypeRep bv (R.typeRep @UnsignedBV)) of
          (Just R.HRefl, _) -> fmap (first SignedBV) . partitionWithOrd . fmap (first BVS.asBV) . resolveFirst t
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
      Just s -> case termSymbolTypeRep s of
        R.SomeTypeRep t@(TFunType a r) -> R.withTypeable t $ PM.insert m s $ goufuncResolve a r l
        _ -> error "Bad"
      Nothing -> error "Bad"

-- helpers
data TFunTypeContainer :: forall k. k -> * where
  TFunTypeContainer :: R.TypeRep a -> R.TypeRep b -> TFunTypeContainer (a =-> b)

tFunTypeView :: R.TypeRep t -> Maybe (TFunTypeContainer t)
tFunTypeView t = case t of
  R.App (R.App arr (ta2' :: R.TypeRep a2)) (tr2' :: R.TypeRep r2) ->
    case R.eqTypeRep arr (R.typeRep @(=->)) of
      Just R.HRefl -> Just $ TFunTypeContainer ta2' tr2'
      Nothing -> Nothing
  _ -> Nothing

pattern TFunType ::
  forall k (t :: k).
  () =>
  forall (a :: *) (b :: *).
  (t ~~ (a =-> b), k ~ *) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep t
pattern TFunType a b <-
  (tFunTypeView -> Just (TFunTypeContainer a b))
  where
    TFunType a b = R.App (R.App (R.typeRep @(=->)) a) b

pattern TFun3Type ::
  forall k (t :: k).
  () =>
  forall (a :: *) (b :: *) (c :: *).
  (t ~~ (a =-> b =-> c), k ~ *) =>
  R.TypeRep a ->
  R.TypeRep b ->
  R.TypeRep c ->
  R.TypeRep t
pattern TFun3Type a b c = TFunType a (TFunType b c)

data SomeTypeRepK1Ty where
  SomeTypeRepK1Ty :: forall (a :: *). R.TypeRep a -> SomeTypeRepK1Ty

someTypeRepK1View :: R.SomeTypeRep -> Maybe SomeTypeRepK1Ty
someTypeRepK1View (R.SomeTypeRep t) =
  case R.eqTypeRep (R.typeRepKind t) (R.typeRepKind (R.typeRep @Bool)) of
    Just R.HRefl -> Just $ SomeTypeRepK1Ty t
    _ -> Nothing

pattern SomeTypeRepK1 ::
  () =>
  forall k (a :: k).
  (k ~ *) =>
  R.TypeRep a ->
  R.SomeTypeRep
pattern SomeTypeRepK1 a <- (someTypeRepK1View -> Just (SomeTypeRepK1Ty a))
