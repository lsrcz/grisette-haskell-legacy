{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Error.Either (mrgRunError) where

import Control.Carrier.Error.Either
import Grisette.Core

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ErrorC e m a)
  where
  mergeStrategy = wrapMergeStrategy mergeStrategy ErrorC (\(ErrorC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ErrorC e m) where
  liftMergeStrategy ms = wrapMergeStrategy (liftMergeStrategy ms) ErrorC (\(ErrorC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ErrorC e m a)
  where
  mrgIte cond (ErrorC t) (ErrorC f) = ErrorC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ErrorC e m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Functor m) =>
  UnionLike bool (ErrorC e m)
  where
  mergeWithStrategy s (ErrorC et) = ErrorC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (ErrorC l) (ErrorC r) = ErrorC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy s a = ErrorC $ mrgSingleWithStrategy s a
  single a = ErrorC $ single a
  unionIf cond (ErrorC t) (ErrorC f) = ErrorC $ unionIf cond t f

mrgRunError ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool exc,
    Mergeable bool a
  ) =>
  ErrorC exc m a ->
  m (Either exc a)
mrgRunError = merge . runError
