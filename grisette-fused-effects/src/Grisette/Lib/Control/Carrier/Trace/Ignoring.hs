{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Trace.Ignoring where

import Control.Carrier.Trace.Ignoring
import Grisette.Core

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a, Functor m) =>
  Mergeable bool (TraceC m a)
  where
  mergingStrategy = wrapStrategy mergingStrategy1 TraceC (\(TraceC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Functor m) => Mergeable1 bool (TraceC m) where
  liftMergingStrategy ms = wrapStrategy (liftMergingStrategy ms) TraceC (\(TraceC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (TraceC m a)
  where
  mrgIte cond (TraceC t) (TraceC f) = TraceC $ mrgIf cond t f

instance
  (SymBoolOp bool, UnionLike bool m, Functor m) =>
  SimpleMergeable1 bool (TraceC m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m, Functor m) =>
  UnionLike bool (TraceC m)
  where
  mergeWithStrategy s (TraceC et) = TraceC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (TraceC l) (TraceC r) = TraceC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy ms a = TraceC $ mrgSingleWithStrategy ms a
  single a = TraceC $ single a
  unionIf cond (TraceC t) (TraceC f) = TraceC $ unionIf cond t f

mrgRunTrace :: (SymBoolOp bool, UnionLike bool m, Mergeable bool a) => TraceC m a -> m a
mrgRunTrace = merge . runTrace
