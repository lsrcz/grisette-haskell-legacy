{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.BitVector (BVConcat (..), BVExtend (..), BVExtract (..)) where

import GHC.TypeNats

class BVConcat bv1 bv2 bv3 | bv1 bv2 -> bv3 where
  bvconcat :: bv1 -> bv2 -> bv3

class BVExtend bv1 bv2 where
  bvzeroExtend :: bv1 -> bv2
  bvsignExtend :: bv1 -> bv2
  bvextend :: bv1 -> bv2

class BVExtract bv1 (ix :: Nat) (w :: Nat) bv2 | bv1 w -> bv2 where
  bvextract :: proxy ix -> proxy w -> bv1 -> bv2
