{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Lib.Control.Carrier.State.Common where

import Control.Effect.State
import Grisette.Core

s :: (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool) => (Int -> Int) -> (Int -> a) -> m a
s fs fv = state $ \st -> (fs st, fv st)

sm ::
  forall sig m bool a.
  (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool (m a)) =>
  bool ->
  (Int -> Int) ->
  (Int -> a) ->
  (Int -> Int) ->
  (Int -> a) ->
  m a
sm cond fs1 fv1 fs2 fv2 = ms cond (s fs1 fv1) (s fs2 fv2)
  where
    SimpleStrategy ms = mergingStrategy :: MergingStrategy bool (m a)

sm1 ::
  forall sig m bool a.
  (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  (Int -> Int) ->
  (Int -> a) ->
  (Int -> Int) ->
  (Int -> a) ->
  m a
sm1 cond fs1 fv1 fs2 fv2 = ms cond (s fs1 fv1) (s fs2 fv2)
  where
    SimpleStrategy ms = mergingStrategy1 :: MergingStrategy bool (m a)

ss ::
  forall sig m bool a.
  (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool (m a)) =>
  bool ->
  (Int -> Int) ->
  (Int -> a) ->
  (Int -> Int) ->
  (Int -> a) ->
  m a
ss cond fs1 fv1 fs2 fv2 = mrgIte cond (s fs1 fv1) (s fs2 fv2)

ss1 ::
  forall sig m bool a.
  (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool a) =>
  bool ->
  (Int -> Int) ->
  (Int -> a) ->
  (Int -> Int) ->
  (Int -> a) ->
  m a
ss1 cond fs1 fv1 fs2 fv2 = mrgIte1 cond (s fs1 fv1) (s fs2 fv2)

su ::
  forall sig m bool a.
  (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool a) =>
  bool ->
  (Int -> Int) ->
  (Int -> a) ->
  (Int -> Int) ->
  (Int -> a) ->
  m a
su cond fs1 fv1 fs2 fv2 = mrgIf cond (s fs1 fv1) (s fs2 fv2)

su' ::
  forall sig m bool a.
  (Has (State Int) sig m, UnionLike bool m, SymBoolOp bool) =>
  bool ->
  (Int -> Int) ->
  (Int -> a) ->
  (Int -> Int) ->
  (Int -> a) ->
  m a
su' cond fs1 fv1 fs2 fv2 = unionIf cond (s fs1 fv1) (s fs2 fv2)
