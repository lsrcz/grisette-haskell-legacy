{-# LANGUAGE AllowAmbiguousTypes #-}

module Grisette.Control.Monad
  ( mrgReturn,
    (>>=~),
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgMsum,
  )
where

import Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Functor

mrgReturn :: forall bool m a. (UnionMOp bool m, Mergeable bool a, Monad m) => a -> m a
mrgReturn = merge . return

(>>=~) :: forall bool m a b. (UnionMOp bool m, Mergeable bool b, Monad m) => m a -> (a -> m b) -> m b
a >>=~ f = merge $ a >>= f

mrgFoldM :: (UnionMOp bool m, Mergeable bool b, Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
mrgFoldM f z0 xs = foldr c mrgReturn xs z0
  where
    c x k z = f z x >>= k

(>>~) :: forall bool m a b. (SymBoolOp bool, UnionMOp bool m, Mergeable bool b, Monad m) => m a -> m b -> m b
a >>~ f = merge $ mrgFmap (const ()) a >> f

mrgMzero :: forall bool m a. (UnionMOp bool m, Mergeable bool a, MonadPlus m) => m a
mrgMzero = merge mzero

mrgMplus :: forall bool m a. (UnionMOp bool m, Mergeable bool a, MonadPlus m) => m a -> m a -> m a
mrgMplus a b = merge $ mplus a b

mrgMsum :: forall bool m a t. (UnionMOp bool m, Mergeable bool a, MonadPlus m, Foldable t) => t (m a) -> m a
mrgMsum = foldr mrgMplus mrgMzero
