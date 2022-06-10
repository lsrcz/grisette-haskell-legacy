{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Writer.Church where

import Control.Carrier.Writer.Church
import Grisette.Core
import Grisette.Lib.Control.Carrier.State.Church

instance
  (SymBoolOp bool, UnionLike bool m) =>
  Mergeable bool (WriterC w m a)
  where
  mergeStrategy = wrapMergeStrategy mergeStrategy WriterC (\(WriterC et) -> et)

instance (SymBoolOp bool, UnionLike bool m) => Mergeable1 bool (WriterC w m) where
  liftMergeStrategy ms = wrapMergeStrategy (liftMergeStrategy ms) WriterC (\(WriterC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable bool (WriterC w m a)
  where
  mrgIte cond (WriterC t) (WriterC f) = WriterC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable1 bool (WriterC w m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  UnionLike bool (WriterC w m)
  where
  mergeWithStrategy ms (WriterC et) = WriterC $ mergeWithStrategy ms et
  mrgIfWithStrategy ms cond (WriterC l) (WriterC r) = WriterC $ mrgIfWithStrategy ms cond l r
  mrgSingleWithStrategy ms a = WriterC $ mrgSingleWithStrategy ms a
  single a = WriterC $ single a
  unionIf cond (WriterC t) (WriterC f) = WriterC $ unionIf cond t f

mrgRunWriter ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool b,
    Monoid w
  ) =>
  (w -> a -> m b) ->
  WriterC w m a ->
  m b
mrgRunWriter c (WriterC m) = mrgRunState c mempty m

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
