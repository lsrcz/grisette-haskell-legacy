{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.State.Church where

import Control.Carrier.State.Church
import Grisette.Core

instance
  (SymBoolOp bool, UnionLike bool m) =>
  Mergeable bool (StateC e m a)
  where
  mergeStrategy = SimpleStrategy $ \cond (StateC l) (StateC r) ->
    StateC $ \k s -> unionIf cond (l k s) (r k s)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  Mergeable1 bool (StateC e m)
  where
  liftMergeStrategy _ = SimpleStrategy $ \cond (StateC l) (StateC r) ->
    StateC $ \k s -> unionIf cond (l k s) (r k s)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable bool (StateC e m a)
  where
  mrgIte bool (StateC l) (StateC r) = StateC $ \k s ->
    unionIf bool (l k s) (r k s)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable1 bool (StateC e m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  UnionLike bool (StateC e m)
  where
  mergeWithStrategy _ = id
  mrgIfWithStrategy _ = unionIf
  mrgSingleWithStrategy _ = single
  single a = StateC $ \k s -> k s a
  unionIf cond (StateC l) (StateC r) =
    StateC $ \k s -> unionIf cond (l k s) (r k s)

mrgRunState :: (SymBoolOp bool, UnionLike bool m, Mergeable bool b) =>
  (s -> a -> m b) -> s -> StateC s m a -> m b
mrgRunState f s = merge . runState f s

mrgEvalState :: (SymBoolOp bool, UnionLike bool m, Mergeable bool a) =>
  s -> StateC s m a -> m a
mrgEvalState = runState (const mrgSingle)

mrgExecState :: (SymBoolOp bool, UnionLike bool m, Mergeable bool s) =>
  s -> StateC s m a -> m s
mrgExecState = runState (const . mrgSingle)
