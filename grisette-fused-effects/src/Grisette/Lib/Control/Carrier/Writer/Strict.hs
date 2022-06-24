{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Writer.Strict where

import Control.Carrier.Writer.Strict
import Grisette.Core
import Grisette.Lib.Control.Carrier.State.Strict

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool w, Mergeable bool a) =>
  Mergeable bool (WriterC w m a)
  where
  mergingStrategy = wrapStrategy mergingStrategy WriterC (\(WriterC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool w, Functor m) => Mergeable1 bool (WriterC w m) where
  liftMergingStrategy ms = wrapStrategy (liftMergingStrategy ms) WriterC (\(WriterC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool w, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (WriterC w m a)
  where
  mrgIte cond (WriterC t) (WriterC f) = WriterC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool w, Functor m) =>
  SimpleMergeable1 bool (WriterC w m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool w, Functor m) =>
  UnionLike bool (WriterC w m)
  where
  mergeWithStrategy s (WriterC et) = WriterC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (WriterC l) (WriterC r) = WriterC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy ms a = WriterC $ mrgSingleWithStrategy ms a
  single a = WriterC $ single a
  unionIf cond (WriterC t) (WriterC f) = WriterC $ unionIf cond t f

mrgRunWriter ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool w,
    Mergeable bool a,
    Monoid w
  ) =>
  WriterC w m a ->
  m (w, a)
mrgRunWriter (WriterC m) = mrgRunState mempty m

mrgExecWriter ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool w,
    Monoid w,
    Functor m
  ) =>
  WriterC w m a ->
  m w
mrgExecWriter (WriterC m) = mrgExecState mempty m
