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

class (SymBoolOp bool) => UnionOp bool (u :: * -> *) | u -> bool where
  single :: a -> u a
  guard :: bool -> u a -> u a -> u a
  singleView :: u a -> Maybe a
  guardView :: u a -> Maybe (bool, u a, u a)
  leftMost :: u a -> a

pattern SingleU :: UnionOp bool u => a -> u a
pattern SingleU x <-
  (singleView -> Just x)
  where
    SingleU x = single x

pattern GuardU :: UnionOp bool u => bool -> u a -> u a -> u a
pattern GuardU c t f <-
  (guardView -> Just (c, t, f))
  where
    GuardU c t f = guard c t f
