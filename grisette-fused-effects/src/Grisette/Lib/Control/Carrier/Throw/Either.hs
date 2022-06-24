{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Throw.Either where

import Control.Carrier.Throw.Either
import Grisette.Core
import Grisette.Lib.Control.Carrier.Error.Either ()

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ThrowC e m a)
  where
  mergingStrategy = wrapStrategy mergingStrategy ThrowC (\(ThrowC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ThrowC e m) where
  liftMergingStrategy ms = wrapStrategy (liftMergingStrategy ms) ThrowC (\(ThrowC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ThrowC e m a)
  where
  mrgIte cond (ThrowC t) (ThrowC f) = ThrowC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ThrowC e m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Functor m) =>
  UnionLike bool (ThrowC e m)
  where
  mergeWithStrategy s (ThrowC et) = ThrowC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (ThrowC l) (ThrowC r) = ThrowC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy ms a = ThrowC $ mrgSingleWithStrategy ms a
  single a = ThrowC $ single a
  unionIf cond (ThrowC t) (ThrowC f) = ThrowC $ unionIf cond t f

mrgRunThrow ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool exc,
    Mergeable bool a
  ) =>
  ThrowC exc m a ->
  m (Either exc a)
mrgRunThrow = merge . runThrow
