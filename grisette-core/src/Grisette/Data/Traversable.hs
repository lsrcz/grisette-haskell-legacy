{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Data.Traversable
  ( mrgTraverse,
    mrgSequenceA,
    mrgFor,
    mrgMapM,
    mrgForM,
    mrgSequence,
  )
where

import Grisette.Control.Monad.Union
import Grisette.Data.Class.Mergeable

mrgTraverse ::
  forall bool a b t f.
  ( Mergeable bool b,
    Mergeable1 bool t,
    MonadUnion bool f,
    Traversable t
  ) =>
  (a -> f b) ->
  t a ->
  f (t b)
mrgTraverse f = withMergeable @bool @t @b $ merge . traverse (merge . f)
{-# INLINE mrgTraverse #-}

mrgSequenceA ::
  forall bool a t f.
  ( Mergeable bool a,
    Mergeable1 bool t,
    MonadUnion bool f,
    Traversable t
  ) =>
  t (f a) ->
  f (t a)
mrgSequenceA = mrgTraverse id
{-# INLINE mrgSequenceA #-}

mrgMapM ::
  forall bool a b t f.
  ( Mergeable bool b,
    Mergeable1 bool t,
    MonadUnion bool f,
    Traversable t
  ) =>
  (a -> f b) ->
  t a ->
  f (t b)
mrgMapM = mrgTraverse
{-# INLINE mrgMapM #-}

mrgSequence ::
  forall bool a t f.
  ( Mergeable bool a,
    Mergeable1 bool t,
    MonadUnion bool f,
    Traversable t
  ) =>
  t (f a) ->
  f (t a)
mrgSequence = mrgSequenceA
{-# INLINE mrgSequence #-}

mrgFor ::
  ( Mergeable bool b,
    Mergeable1 bool t,
    Traversable t,
    MonadUnion bool m
  ) =>
  t a ->
  (a -> m b) ->
  m (t b)
mrgFor = flip mrgTraverse

mrgForM ::
  ( Mergeable bool b,
    Mergeable1 bool t,
    Traversable t,
    MonadUnion bool m
  ) =>
  t a ->
  (a -> m b) ->
  m (t b)
mrgForM = flip mapM
