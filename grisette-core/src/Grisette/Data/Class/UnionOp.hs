{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Class.UnionOp
  ( UnionOp (..),
    pattern SingleU,
    pattern GuardU,
  )
where

import Grisette.Data.Class.Bool
import Data.Kind

-- | Basic operations for union-like containers.
-- These operations does not ensure the result to be merged.
class (SymBoolOp bool) => UnionOp bool (u :: Type -> Type) | u -> bool where
  -- | Wrap a single value in the union.
  single :: a -> u a
  -- | If-then-else on two union values.
  guard :: bool -> u a -> u a -> u a
  -- | Pattern match to extract single values.
  singleView :: u a -> Maybe a
  -- | Pattern match to extract guard values.
  guardView :: u a -> Maybe (bool, u a, u a)
  -- | The leftmost value in the union.
  leftMost :: u a -> a

-- | Pattern match to extract single values with 'singleView'.
pattern SingleU :: UnionOp bool u => a -> u a
pattern SingleU x <-
  (singleView -> Just x)
  where
    SingleU x = single x

-- | Pattern match to extract guard values with 'guardView'
pattern GuardU :: UnionOp bool u => bool -> u a -> u a -> u a
pattern GuardU c t f <-
  (guardView -> Just (c, t, f))
  where
    GuardU c t f = guard c t f
