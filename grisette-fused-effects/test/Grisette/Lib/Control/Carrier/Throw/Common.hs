{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Lib.Control.Carrier.Throw.Common where

import Control.Effect.Throw
import Grisette.Core

e :: (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool) => Either a b -> m b
e = liftEither

em ::
  forall sig m bool a b.
  (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool (m b)) =>
  bool ->
  Either a b ->
  Either a b ->
  m b
em cond e1 e2 = ms cond (e e1) (e e2)
  where
    SimpleStrategy ms = mergeStrategy :: MergeStrategy bool (m b)

em1 ::
  forall sig m bool a b.
  (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool b) =>
  bool ->
  Either a b ->
  Either a b ->
  m b
em1 cond e1 e2 = ms cond (e e1) (e e2)
  where
    SimpleStrategy ms = mergeStrategy1 :: MergeStrategy bool (m b)

es ::
  forall sig m bool a b.
  (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool (m b)) =>
  bool ->
  Either a b ->
  Either a b ->
  m b
es cond e1 e2 = mrgIte cond (e e1) (e e2)

es1 ::
  forall sig m bool a b.
  (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool, SimpleMergeable bool b) =>
  bool ->
  Either a b ->
  Either a b ->
  m b
es1 cond e1 e2 = mrgIte1 cond (e e1) (e e2)

eu ::
  forall sig m bool a b.
  (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool, Mergeable bool b) =>
  bool ->
  Either a b ->
  Either a b ->
  m b
eu cond e1 e2 = mrgIf cond (e e1) (e e2)

eu' ::
  forall sig m bool a b.
  (Has (Throw a) sig m, UnionLike bool m, SymBoolOp bool) =>
  bool ->
  Either a b ->
  Either a b ->
  m b
eu' cond e1 e2 = unionIf cond (e e1) (e e2)
