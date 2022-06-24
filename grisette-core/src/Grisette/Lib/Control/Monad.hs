{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Lib.Control.Monad
  ( mrgReturnWithStrategy,
    mrgBindWithStrategy,
    mrgReturn,
    (>>=~),
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgFmap,
  )
where

import Control.Monad
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.Core.Control.Monad.Union
import Grisette.Lib.Data.Foldable

-- | 'return' with 'Mergeable' knowledge propagation.
mrgReturnWithStrategy :: (MonadUnion bool u) => MergingStrategy bool a -> a -> u a
mrgReturnWithStrategy s = mergeWithStrategy s . return

-- | '>>=' with 'Mergeable' knowledge propagation.
mrgBindWithStrategy :: (MonadUnion bool u) => MergingStrategy bool b -> u a -> (a -> u b) -> u b
mrgBindWithStrategy s a f = mergeWithStrategy s $ a >>= f

-- | 'return' with 'Mergeable' knowledge propagation.
mrgReturn :: (MonadUnion bool u, Mergeable bool a) => a -> u a
mrgReturn = merge . return

-- | '>>=' with 'Mergeable' knowledge propagation.
(>>=~) :: (MonadUnion bool u, Mergeable bool b) => u a -> (a -> u b) -> u b
a >>=~ f = merge $ a >>= f

-- | 'foldM' with 'Mergeable' knowledge propagation.
mrgFoldM :: (MonadUnion bool m, Mergeable bool b, Foldable t) => (b -> a -> m b) -> b -> t a -> m b
mrgFoldM = mrgFoldlM

-- | '>>' with 'Mergeable' knowledge propagation.
--
-- This is usually more efficient than calling the original '>>' and merge the results.
(>>~) :: forall bool m a b. (SymBoolOp bool, MonadUnion bool m, Mergeable bool b) => m a -> m b -> m b
a >>~ f = merge $ mrgFmap (const ()) a >> f

-- | 'mzero' with 'Mergeable' knowledge propagation.
mrgMzero :: forall bool m a. (MonadUnion bool m, Mergeable bool a, MonadPlus m) => m a
mrgMzero = merge mzero

-- | 'mplus' with 'Mergeable' knowledge propagation.
mrgMplus :: forall bool m a. (MonadUnion bool m, Mergeable bool a, MonadPlus m) => m a -> m a -> m a
mrgMplus a b = merge $ mplus a b

-- | 'fmap' with 'Mergeable' knowledge propagation.
mrgFmap :: (MonadUnion bool f, Mergeable bool b, Functor f) => (a -> b) -> f a -> f b
mrgFmap f a = merge $ fmap f a

