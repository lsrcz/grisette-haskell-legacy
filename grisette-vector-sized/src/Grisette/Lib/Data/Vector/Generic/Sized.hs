{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Grisette.Lib.Data.Vector.Generic.Sized where

import Data.Functor.Classes
import Data.Typeable
import qualified Data.Vector.Generic as VGeneric
import qualified Data.Vector.Generic.Sized as VSized
import GHC.TypeNats
import Grisette.Core
import Unsafe.Coerce

#if MIN_VERSION_base(4,16,0)
#else
import GHC.Natural
#endif

newtype NatRepr (n::Nat) = NatRepr Natural

knownNat :: forall n. KnownNat n => NatRepr n
knownNat = NatRepr (natVal (Proxy @n))

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

unsafeLeqProof :: LeqProof m n
unsafeLeqProof = unsafeCoerce (LeqProof @0 @0)
{-# NOINLINE unsafeLeqProof #-}

-- | Assert a proof of equality between two types.
-- This is unsafe if used improperly, so use this with caution!
unsafeAxiom :: forall a b. a :~: b
unsafeAxiom = unsafeCoerce (Refl @a)
{-# NOINLINE unsafeAxiom #-} -- Note [Mark unsafe axioms as NOINLINE]

data IsZeroNat n where
  ZeroNat    :: IsZeroNat 0
  NonZeroNat :: IsZeroNat (n+1)

isZeroNat :: NatRepr n -> IsZeroNat n
isZeroNat (NatRepr 0) = unsafeCoerce ZeroNat
isZeroNat (NatRepr _) = unsafeCoerce NonZeroNat

-- | Every nat is either zero or >= 1.
isZeroOrGT1 :: NatRepr n -> Either (n :~: 0) (LeqProof 1 n)
isZeroOrGT1 n =
  case isZeroNat n of
    ZeroNat    -> Left Refl
    NonZeroNat -> Right $ unsafeLeqProof

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    Mergeable bool t,
    KnownNat m,
    VGeneric.Vector v t,
    VGeneric.Vector v (MergingStrategy bool t),
    Typeable v,
    Functor v,
    Eq1 v,
    Ord1 v,
    Show1 v,
    Foldable v
  ) =>
  Mergeable bool (VSized.Vector v m t)
  where
  mergingStrategy = case (isZeroOrGT1 (knownNat @m), mergingStrategy :: MergingStrategy bool t) of
    (Left Refl, _) -> SimpleStrategy $ \_ v _ -> v
    (Right LeqProof, SimpleStrategy m) -> SimpleStrategy $ \cond -> VSized.zipWith (m cond)
    (Right LeqProof, SortedStrategy _ _) ->
      SortedStrategy (buildStrategyList @bool mergingStrategy) $ \(StrategyList _ strategies) ->
        let s :: VSized.Vector v m (MergingStrategy bool t) = unsafeCoerce strategies
            allSimple = all (\case SimpleStrategy _ -> True; _ -> False) s
         in if allSimple
              then SimpleStrategy $ \cond l r ->
                VSized.zipWith3 (\(SimpleStrategy f) l1 r1 -> f cond l1 r1 :: t) s l r ::
                  VSized.Vector v m t
              else NoStrategy
    (Right LeqProof, NoStrategy) -> NoStrategy

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    VGeneric.Vector v t
  ) =>
  Mergeable bool (VSized.Vector v 0 t)
  where
  mergingStrategy = SimpleStrategy $ \_ v _ -> v

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    SimpleMergeable bool t,
    KnownNat m,
    VGeneric.Vector v t,
    VGeneric.Vector v (MergingStrategy bool t),
    Typeable v,
    Functor v,
    Eq1 v,
    Ord1 v,
    Show1 v,
    Foldable v
  ) =>
  SimpleMergeable bool (VSized.Vector v m t)
  where
  mrgIte cond = VSized.zipWith (mrgIte cond)

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    VGeneric.Vector v t
  ) =>
  SimpleMergeable bool (VSized.Vector v 0 t)
  where
  mrgIte _ t _ = t

instance
  ( Evaluate model t,
    KnownNat m,
    VGeneric.Vector v t
  ) =>
  Evaluate model (VSized.Vector v m t)
  where
  evaluate fillDefault model = VSized.map (evaluate fillDefault model)

instance
  ( Monoid symbolSet,
    ExtractSymbolics symbolSet t,
    KnownNat m,
    VGeneric.Vector v t
  ) =>
  ExtractSymbolics symbolSet (VSized.Vector v m t)
  where
  extractSymbolics = VSized.foldl' (\acc v -> acc <> extractSymbolics v) mempty

instance (KnownNat m, SEq bool t, SymBoolOp bool, VGeneric.Vector v t) =>
  SEq bool (VSized.Vector v m t) where
  a ==~ b = VSized.toList a ==~ VSized.toList b

instance (KnownNat m, SOrd bool t, SymBoolOp bool, VGeneric.Vector v t) =>
  SOrd bool (VSized.Vector v m t) where
  a <=~ b = VSized.toList a <=~ VSized.toList b
  a <~ b = VSized.toList a <~ VSized.toList b
  a >=~ b = VSized.toList a >=~ VSized.toList b
  a >~ b = VSized.toList a >~ VSized.toList b
  symCompare a b = symCompare (VSized.toList a) (VSized.toList b)

instance (KnownNat m, ToCon a b, VGeneric.Vector v a, VGeneric.Vector v b) =>
  ToCon (VSized.Vector v m a) (VSized.Vector v m b) where
  toCon v = VSized.forM v toCon

instance (KnownNat m, ToSym a b, VGeneric.Vector v a, VGeneric.Vector v b) =>
  ToSym (VSized.Vector v m a) (VSized.Vector v m b) where
  toSym = VSized.map toSym 