{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.State.Strict where

import Control.Carrier.State.Strict
import Grisette.Core

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateC s m a)
  where
  mergeStrategy = wrapMergeStrategy (liftMergeStrategy mergeStrategy1) StateC (\(StateC f) -> f)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) =>
  Mergeable1 bool (StateC s m)
  where
  liftMergeStrategy s = wrapMergeStrategy (liftMergeStrategy (liftMergeStrategy (liftMergeStrategy s))) StateC (\(StateC f) -> f)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionLike bool m) =>
  SimpleMergeable bool (StateC s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m) =>
  SimpleMergeable1 bool (StateC s m)
  where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m) =>
  UnionLike bool (StateC s m)
  where
  mergeWithStrategy ms (StateC f) = StateC $ mergeWithStrategy (liftMergeStrategy ms) . f
  mrgIfWithStrategy s cond (StateC l) (StateC r) = StateC $ \v -> mrgIfWithStrategy (liftMergeStrategy s) cond (l v) (r v)
  mrgSingleWithStrategy ms a = StateC $ \s -> mrgSingleWithStrategy (liftMergeStrategy ms) (s, a)
  single a = StateC $ \s -> single (s, a)
  unionIf cond (StateC l) (StateC r) = StateC $ \s -> unionIf cond (l s) (r s)

mrgRunState :: (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionLike bool m) => s -> StateC s m a -> m (s, a)
mrgRunState s = merge . runState s

mrgEvalState :: (SymBoolOp bool, Mergeable bool a, UnionLike bool m, Functor m) => s -> StateC s m a -> m a
mrgEvalState s = merge . fmap snd . runState s

mrgExecState :: (SymBoolOp bool, Mergeable bool s, UnionLike bool m, Functor m) => s -> StateC s m a -> m s
mrgExecState s = merge . fmap fst . runState s

