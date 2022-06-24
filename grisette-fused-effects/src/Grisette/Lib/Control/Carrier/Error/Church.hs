{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Error.Church (mrgRunError) where

import Control.Carrier.Error.Church
import Grisette.Core

instance
  (SymBoolOp bool, UnionLike bool m) =>
  Mergeable bool (ErrorC e m a)
  where
  mergingStrategy = SimpleStrategy $ \cond (ErrorC l) (ErrorC r) ->
    ErrorC $ \ef af -> unionIf cond (l ef af) (r ef af)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  Mergeable1 bool (ErrorC e m)
  where
  liftMergingStrategy _ = SimpleStrategy $ \cond (ErrorC l) (ErrorC r) ->
    ErrorC $ \ef af -> unionIf cond (l ef af) (r ef af)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable bool (ErrorC e m a)
  where
  mrgIte bool (ErrorC l) (ErrorC r) = ErrorC $ \ef af ->
    unionIf bool (l ef af) (r ef af)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable1 bool (ErrorC e m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  UnionLike bool (ErrorC e m)
  where
  mergeWithStrategy _ = id
  mrgIfWithStrategy _ = unionIf
  mrgSingleWithStrategy _ = single
  single a = ErrorC $ \_ leaf -> leaf a
  unionIf cond (ErrorC l) (ErrorC r) =
    ErrorC $ \ef af -> unionIf cond (l ef af) (r ef af)

mrgRunError ::
  (SymBoolOp bool, UnionLike bool m, Mergeable bool b) =>
  (e -> m b) ->
  (a -> m b) ->
  ErrorC e m a ->
  m b
mrgRunError f leaf = runError (merge . f) (merge . leaf)
