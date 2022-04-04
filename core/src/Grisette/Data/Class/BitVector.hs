{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.BitVector
  ( BVConcat (..),
    BVExtend (..),
    BVSelect (..),
    bvextract,
  )
where

import Data.Proxy
import GHC.TypeNats

-- | Bitwise concatenation ('bvconcat') of the given bitvector values.
class BVConcat bv1 bv2 bv3 | bv1 bv2 -> bv3 where
  -- | Bitwise concatenation of the given bitvector values.
  bvconcat :: bv1 -> bv2 -> bv3

-- | Bitwise extension of the given bitvector values.
class BVExtend bv1 (n :: Nat) bv2 | bv1 n -> bv2 where
  -- | Bitwise zero extension of the given bitvector values.
  bvzeroExtend ::
    -- | Desired output width
    proxy n ->
    -- | Bitvector to extend
    bv1 ->
    bv2

  -- | Bitwise signed extension of the given bitvector values.
  bvsignExtend ::
    -- | Desired output width
    proxy n ->
    -- | Bitvector to extend
    bv1 ->
    bv2

  -- | Bitwise extension of the given bitvector values. Signedness is determined by the input bitvector type.
  bvextend ::
    -- | Desired output width
    proxy n ->
    -- | Bitvector to extend
    bv1 ->
    bv2

-- | Slicing out a smaller bitvector from a larger one, selecting a slice with width @w@ starting from index @ix@.
class BVSelect bv1 (ix :: Nat) (w :: Nat) bv2 | bv1 w -> bv2 where
  -- | Slicing out a smaller bitvector from a larger one, selecting a slice with width @w@ starting from index @ix@.
  bvselect ::
    -- | Index to start selecting from
    proxy ix ->
    -- | Desired output width, @0 <= ix@ and @ix + w < n@ must hold where @n@ is the size of the input bitvector
    proxy w ->
    -- | Bitvector to select from
    bv1 ->
    bv2

-- | Extract a smaller bitvector from a larger one from bits @i@ down to @j@.
bvextract ::
  forall proxy i j bv1 bv2.
  (BVSelect bv1 j (i - j) bv2) =>
  -- | The start position to extract from, @0 <= i < n@ must hold where @n@ is the size of the output bitvector
  proxy i ->
  -- | The end position to extract from, @0 <= j <= i@ must hold
  proxy j ->
  -- | Bitvector to extract from
  bv1 ->
  bv2
bvextract _ _ = bvselect (Proxy @j) (Proxy @(i - j))
