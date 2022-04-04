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

class BVConcat bv1 bv2 bv3 | bv1 bv2 -> bv3 where
  bvconcat :: bv1 -> bv2 -> bv3

class BVExtend bv1 (n :: Nat) bv2 | bv1 n -> bv2 where
  bvzeroExtend :: proxy n -> bv1 -> bv2
  bvsignExtend :: proxy n -> bv1 -> bv2
  bvextend :: proxy n -> bv1 -> bv2

class BVSelect bv1 (ix :: Nat) (w :: Nat) bv2 | bv1 w -> bv2 where
  bvselect :: proxy ix -> proxy w -> bv1 -> bv2

bvextract :: forall proxy i j bv1 bv2. (BVSelect bv1 j (i - j) bv2) => proxy i -> proxy j -> bv1 -> bv2
bvextract _ _ = bvselect (Proxy @j) (Proxy @(i - j))
