{-# LANGUAGE RankNTypes #-}

module Grisette.Data.Foldable
  ( mrgFoldlM,
    mrgFoldrM,
    mrgTraverse_,
    mrgFor_,
    mrgMapM_,
    mrgForM_,
    mrgSequence_,
    mrgMsum,
  )
where

import Control.Monad
import {-# SOURCE #-} Grisette.Control.Monad
import Grisette.Control.Monad.Union
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable

-- | 'foldlM' with 'Mergeable' knowledge propagation.
mrgFoldlM :: (MonadUnion bool m, Mergeable bool b, Foldable t) => (b -> a -> m b) -> b -> t a -> m b
mrgFoldlM f z0 xs = foldr c mrgReturn xs z0
  where
    c x k z = merge (f z x) >>= k

mrgFoldrM :: (MonadUnion bool m, Mergeable bool b, Foldable t) => (a -> b -> m b) -> b -> t a -> m b
mrgFoldrM f z0 xs = foldl c mrgReturn xs z0
  where
    c k x z = merge (f x z) >>= k

mrgTraverse_ :: (SymBoolOp bool, MonadUnion bool m, Foldable t) => (a -> m b) -> t a -> m ()
mrgTraverse_ f = foldr c (mrgReturn ())
  where
    c x k = f x >> k

mrgFor_ :: (SymBoolOp bool, MonadUnion bool m, Foldable t) => t a -> (a -> m b) -> m ()
mrgFor_ = flip mrgTraverse_

mrgMapM_ :: (SymBoolOp bool, MonadUnion bool m, Foldable t) => (a -> m b) -> t a -> m ()
mrgMapM_ = mrgTraverse_

mrgForM_ :: (SymBoolOp bool, MonadUnion bool m, Foldable t) => t a -> (a -> m b) -> m ()
mrgForM_ = flip mrgMapM_

mrgSequence_ :: (SymBoolOp bool, Foldable t, MonadUnion bool m) => t (m a) -> m ()
mrgSequence_ = foldr c (mrgReturn ())
  where
    c m k = m >> k

-- | 'msum' with 'Mergeable' knowledge propagation.
mrgMsum :: forall bool m a t. (MonadUnion bool m, Mergeable bool a, MonadPlus m, Foldable t) => t (m a) -> m a
mrgMsum = foldr mrgMplus mrgMzero