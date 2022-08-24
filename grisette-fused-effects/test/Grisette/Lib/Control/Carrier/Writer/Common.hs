{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Grisette.Lib.Control.Carrier.Writer.Common where

import Control.Effect.Writer
import Data.Monoid
import Grisette.Core

w :: (Has (Writer (Sum Int)) sig m, UnionLike bool m, SymBoolOp bool) => Sum Int -> a -> m a
w s x = do
  tell s
  return x

wm ::
  forall sig m bool a.
  ( Has (Writer (Sum Int)) sig m,
    UnionLike bool m,
    SymBoolOp bool,
    Mergeable bool (m a)
  ) =>
  bool ->
  Sum Int ->
  a ->
  Sum Int ->
  a ->
  m a
wm cond s1 x1 s2 x2 = ms cond (w s1 x1) (w s2 x2)
  where
    SimpleStrategy ms = mergingStrategy :: MergingStrategy bool (m a)

wm1 ::
  forall sig m bool a.
  (Has (Writer (Sum Int)) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  Sum Int ->
  a ->
  Sum Int ->
  a ->
  m a
wm1 cond s1 x1 s2 x2 = ms cond (w s1 x1) (w s2 x2)
  where
    SimpleStrategy ms = mergingStrategy1 :: MergingStrategy bool (m a)

ws ::
  forall sig m bool a.
  (Has (Writer (Sum Int)) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool (m a)) =>
  bool ->
  Sum Int ->
  a ->
  Sum Int ->
  a ->
  m a
ws cond s1 x1 s2 x2 = mrgIte cond (w s1 x1) (w s2 x2)

ws1 ::
  forall sig m bool a.
  (Has (Writer (Sum Int)) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool a) =>
  bool ->
  Sum Int ->
  a ->
  Sum Int ->
  a ->
  m a
ws1 cond s1 x1 s2 x2 = mrgIte1 cond (w s1 x1) (w s2 x2)

wu ::
  forall sig m bool a.
  (Has (Writer (Sum Int)) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  Sum Int ->
  a ->
  Sum Int ->
  a ->
  m a
wu cond s1 x1 s2 x2 = mrgIf cond (w s1 x1) (w s2 x2)

wu' ::
  forall sig m bool a.
  (Has (Writer (Sum Int)) sig m, UnionLike bool m, SymBoolOp bool) =>
  bool ->
  Sum Int ->
  a ->
  Sum Int ->
  a ->
  m a
wu' cond s1 x1 s2 x2 = unionIf cond (w s1 x1) (w s2 x2)
