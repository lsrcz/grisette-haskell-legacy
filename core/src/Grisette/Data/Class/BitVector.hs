{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.BitVector (BVConcat (..), BVExt (..), BVExtract (..)) where

import GHC.TypeNats

class BVConcat bv1 bv2 bv3 | bv1 bv2 -> bv3 where
  bvconcat :: bv1 -> bv2 -> bv3

class BVExt bv1 (n :: Nat) bv2 | bv1 n -> bv2 where
  bvzext :: proxy n -> bv1 -> bv2
  bvsext :: proxy n -> bv1 -> bv2
  bvext :: proxy n -> bv1 -> bv2

class BVExtract bv1 (ix :: Nat) (w :: Nat) bv2 | bv1 w -> bv2 where
  bvextract :: proxy ix -> proxy w -> bv1 -> bv2
