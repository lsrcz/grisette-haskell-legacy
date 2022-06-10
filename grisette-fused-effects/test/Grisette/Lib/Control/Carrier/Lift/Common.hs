{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Lib.Control.Carrier.Lift.Common where

import Grisette.Core

l :: (UnionLike bool m, SymBoolOp bool) => a -> m a
l = single

lm ::
  forall m bool a.
  (UnionLike bool m, SymBoolOp bool, Mergeable bool (m a)) =>
  bool ->
  a ->
  a ->
  m a
lm cond v1 v2 = ms cond (l v1) (l v2)
  where
    SimpleStrategy ms = mergeStrategy :: MergeStrategy bool (m a)

lm1 ::
  forall m bool a.
  (UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  a ->
  a ->
  m a
lm1 cond v1 v2 = ms cond (l v1) (l v2)
  where
    SimpleStrategy ms = mergeStrategy1 :: MergeStrategy bool (m a)

ls ::
  forall m bool a.
  (UnionLike bool m, SymBoolOp bool, SimpleMergeable bool (m a)) =>
  bool ->
  a ->
  a ->
  m a
ls cond v1 v2 = mrgIte cond (l v1) (l v2)

ls1 ::
  forall m bool a.
  (UnionLike bool m, SymBoolOp bool, SimpleMergeable bool a) =>
  bool ->
  a ->
  a ->
  m a
ls1 cond v1 v2 = mrgIte1 cond (l v1) (l v2)

lu ::
  forall m bool a.
  (UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  a ->
  a ->
  m a
lu cond v1 v2 = mrgIf cond (l v1) (l v2)

lu' ::
  forall m bool a.
  (UnionLike bool m, SymBoolOp bool) =>
  bool ->
  a ->
  a ->
  m a
lu' cond v1 v2 = unionIf cond (l v1) (l v2)
