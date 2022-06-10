{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Fail.Either where

import Control.Carrier.Fail.Either
import Grisette.Core
import Grisette.Lib.Control.Carrier.Throw.Either ()

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) =>
  Mergeable bool (FailC m a)
  where
  mergeStrategy = wrapMergeStrategy mergeStrategy FailC (\(FailC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Functor m) => Mergeable1 bool (FailC m) where
  liftMergeStrategy ms = wrapMergeStrategy (liftMergeStrategy ms) FailC (\(FailC et) -> et)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (FailC m a)
  where
  mrgIte cond (FailC t) (FailC f) = FailC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionLike bool m, Functor m) =>
  SimpleMergeable1 bool (FailC m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionLike bool m, Functor m) =>
  UnionLike bool (FailC m)
  where
  mergeWithStrategy s (FailC et) = FailC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (FailC l) (FailC r) = FailC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy s a = FailC $ mrgSingleWithStrategy s a
  single a = FailC $ single a
  unionIf cond (FailC t) (FailC f) = FailC $ unionIf cond t f

mrgRunFail ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool a
  ) =>
  FailC m a ->
  m (Either String a)
mrgRunFail = merge . runFail
