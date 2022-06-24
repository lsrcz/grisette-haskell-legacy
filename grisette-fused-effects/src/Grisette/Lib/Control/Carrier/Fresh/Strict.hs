{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Fresh.Strict where

import Control.Carrier.Fresh.Strict
import Grisette.Core
import Grisette.Lib.Control.Carrier.State.Strict

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) =>
  Mergeable bool (FreshC m a)
  where
  mergingStrategy = wrapStrategy mergingStrategy1 FreshC (\(FreshC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Functor m) => Mergeable1 bool (FreshC m) where
  liftMergingStrategy ms = wrapStrategy (liftMergingStrategy ms) FreshC (\(FreshC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (FreshC m a)
  where
  mrgIte cond (FreshC t) (FreshC f) = FreshC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionLike bool m, Functor m) =>
  SimpleMergeable1 bool (FreshC m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m, Functor m) =>
  UnionLike bool (FreshC m)
  where
  mergeWithStrategy s (FreshC et) = FreshC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (FreshC l) (FreshC r) = FreshC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy ms a = FreshC $ mrgSingleWithStrategy ms a
  single a = FreshC $ single a
  unionIf cond (FreshC t) (FreshC f) = FreshC $ unionIf cond t f

mrgRunFresh ::
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a) =>
  Int ->
  FreshC m a ->
  m (Int, a)
mrgRunFresh n (FreshC m) = mrgRunState n m

mrgEvalFresh ::
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a, Functor m) =>
  Int ->
  FreshC m a ->
  m a
mrgEvalFresh n (FreshC m) = mrgEvalState n m
