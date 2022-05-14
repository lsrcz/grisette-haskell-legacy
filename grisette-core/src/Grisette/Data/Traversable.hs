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

-- | 'traverse' with 'Mergeable' knowledge propagation.
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

-- | 'sequenceA' with 'Mergeable' knowledge propagation.
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

-- | 'mapM' with 'Mergeable' knowledge propagation.
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

-- | 'sequence' with 'Mergeable' knowledge propagation.
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

-- | 'for' with 'Mergeable' knowledge propagation.
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

-- | 'forM' with 'Mergeable' knowledge propagation.
mrgForM ::
  ( Mergeable bool b,
    Mergeable1 bool t,
    Traversable t,
    MonadUnion bool m
  ) =>
  t a ->
  (a -> m b) ->
  m (t b)
mrgForM = flip mrgMapM
