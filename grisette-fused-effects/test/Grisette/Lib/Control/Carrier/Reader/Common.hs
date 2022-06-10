{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Lib.Control.Carrier.Reader.Common where

import Control.Effect.Reader
import Grisette.Core

r :: (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool) => (Int -> a) -> m a
r = asks

rm ::
  forall sig m bool a.
  (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool (m a)) =>
  bool ->
  (Int -> a) ->
  (Int -> a) ->
  m a
rm cond f1 f2 = ms cond (r f1) (r f2)
  where
    SimpleStrategy ms = mergeStrategy :: MergeStrategy bool (m a)

rm1 ::
  forall sig m bool a.
  (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  (Int -> a) ->
  (Int -> a) ->
  m a
rm1 cond f1 f2 = ms cond (r f1) (r f2)
  where
    SimpleStrategy ms = mergeStrategy1 :: MergeStrategy bool (m a)

rs ::
  forall sig m bool a.
  (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool (m a)) =>
  bool ->
  (Int -> a) ->
  (Int -> a) ->
  m a
rs cond f1 f2 = mrgIte cond (r f1) (r f2)

rs1 ::
  forall sig m bool a.
  (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool a) =>
  bool ->
  (Int -> a) ->
  (Int -> a) ->
  m a
rs1 cond f1 f2 = mrgIte1 cond (r f1) (r f2)

ru ::
  forall sig m bool a.
  (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  (Int -> a) ->
  (Int -> a) ->
  m a
ru cond f1 f2 = mrgIf cond (r f1) (r f2)

ru' ::
  forall sig m bool a.
  (Has (Reader Int) sig m, UnionLike bool m, SymBoolOp bool) =>
  bool ->
  (Int -> a) ->
  (Int -> a) ->
  m a
ru' cond f1 f2 = unionIf cond (r f1) (r f2)
