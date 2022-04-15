{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Control.Monad
  ( mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgMsum,
    mrgFmap,
    MonadUnion (..),
    getSingle,
  )
where

import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Except
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import Control.Monad.Trans.Maybe
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Control.Monad.Identity

-- | Class for monads that support union-like operations and 'Mergeable' knowledge propagation.
-- All the functions should propagate the 'Mergeable' knowledge.

class (UnionSimpleMergeable1 bool u, Monad u) => MonadUnion bool u | u -> bool where
  -- | Perform merge on the monad.
  merge :: (Mergeable bool a) => u a -> u a
  -- | 'return' with 'Mergeable' knowledge propagation.
  mrgReturn :: (Mergeable bool a) => a -> u a
  mrgReturn = merge . return
  -- | Symbolic if statement. 
  mrgIf :: (Mergeable bool a) => bool -> u a -> u a -> u a
  mrgIf = mrgIteu1
  -- | '>>=' with 'Mergeable' knowledge propagation.
  (>>=~) :: (Mergeable bool b) => u a -> (a -> u b) -> u b
  a >>=~ f = merge $ a >>= f

-- | Extract the value from a union-like monad if the value has a simply mergeable type.
--
-- 'Grisette.Data.Class.UnionOp.guard' will not merge the results.
-- 'getSingle' will merge it and extract the single value.
--
-- >>> guard (ssymb "a") (return $ ssymb "b") (return $ ssymb "c") :: UnionM SymBool
-- UAny (Guard a (Single b) (Single c))
-- >>> getSingle it
-- (ite a b c)
getSingle :: forall bool u a. (SimpleMergeable bool a, MonadUnion bool u, UnionOp bool u) => u a -> a
getSingle u = case merge u of
  SingleU x -> x
  _ -> error "Should not happen"

instance (SymBoolOp bool, MonadUnion bool m) => MonadUnion bool (MaybeT m) where
  merge (MaybeT v) = MaybeT $ merge @bool v
  mrgReturn v = MaybeT $ mrgReturn $ return v
  mrgIf cond (MaybeT t) (MaybeT f) = MaybeT $ mrgIf cond t f

instance
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool e, Functor m) =>
  MonadUnion bool (ExceptT e m)
  where
  merge (ExceptT v) = ExceptT $ merge v
  mrgReturn v = ExceptT $ mrgReturn $ return v
  mrgIf cond (ExceptT t) (ExceptT f) = ExceptT $ mrgIf cond t f

instance
  (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus, Functor sus) =>
  MonadUnion bool (Coroutine sus m)
  where
  merge ((Coroutine v) :: Coroutine sus m a) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ merge @bool v
  mrgReturn (v :: a) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ mrgReturn $ return v
  mrgIf cond ((Coroutine t) :: Coroutine sus m a) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ mrgIf cond t f

instance
  (SymBoolOp bool, Mergeable bool s, MonadUnion bool m) =>
  MonadUnion bool (StateLazy.StateT s m)
  where
  merge (StateLazy.StateT f) = StateLazy.StateT $ \v -> merge $ f v
  mrgReturn v = StateLazy.StateT $ \s -> mrgReturn (v, s)
  mrgIf cond (StateLazy.StateT t) (StateLazy.StateT f) =
    StateLazy.StateT $ \s -> mrgIf cond (t s) (f s)

instance
  (SymBoolOp bool, Mergeable bool s, MonadUnion bool m) =>
  MonadUnion bool (StateStrict.StateT s m)
  where
  merge (StateStrict.StateT f) = StateStrict.StateT $ \v -> merge $ f v
  mrgReturn v = StateStrict.StateT $ \s -> mrgReturn (v, s)
  mrgIf cond (StateStrict.StateT t) (StateStrict.StateT f) =
    StateStrict.StateT $ \s -> mrgIf cond (t s) (f s)

instance
  (Monoid s, SymBoolOp bool, Mergeable bool s, MonadUnion bool m) =>
  MonadUnion bool (WriterLazy.WriterT s m)
  where
  merge (WriterLazy.WriterT f) = WriterLazy.WriterT $ merge f
  mrgReturn v = WriterLazy.WriterT $ mrgReturn (v, mempty)
  mrgIf cond (WriterLazy.WriterT t) (WriterLazy.WriterT f) =
    WriterLazy.WriterT $ mrgIf cond t f

instance
  (Monoid s, SymBoolOp bool, Mergeable bool s, MonadUnion bool m) =>
  MonadUnion bool (WriterStrict.WriterT s m)
  where
  merge (WriterStrict.WriterT f) = WriterStrict.WriterT $ merge f
  mrgReturn v = WriterStrict.WriterT $ mrgReturn (v, mempty)
  mrgIf cond (WriterStrict.WriterT t) (WriterStrict.WriterT f) =
    WriterStrict.WriterT $ mrgIf cond t f

instance
  (SymBoolOp bool, MonadUnion bool m) =>
  MonadUnion bool (ReaderT s m)
  where
  merge (ReaderT f) = ReaderT $ \v -> merge $ f v
  mrgReturn v = ReaderT $ \_ -> mrgReturn v
  mrgIf cond (ReaderT t) (ReaderT f) =
    ReaderT $ \s -> mrgIf cond (t s) (f s)

instance (SymBoolOp bool, MonadUnion bool m) => MonadUnion bool (IdentityT m) where
  merge (IdentityT f) = IdentityT (merge f)
  mrgReturn v = IdentityT $ mrgReturn v
  mrgIf cond (IdentityT t) (IdentityT f) = IdentityT $ mrgIf cond t f

-- | 'foldM' with 'Mergeable' knowledge propagation.
mrgFoldM :: (MonadUnion bool m, Mergeable bool b, Foldable t) => (b -> a -> m b) -> b -> t a -> m b
mrgFoldM f z0 xs = foldr c mrgReturn xs z0
  where
    c x k z = merge (f z x) >>= k

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

-- | 'msum' with 'Mergeable' knowledge propagation.
mrgMsum :: forall bool m a t. (MonadUnion bool m, Mergeable bool a, MonadPlus m, Foldable t) => t (m a) -> m a
mrgMsum = foldr mrgMplus mrgMzero

-- | 'fmap' with 'Mergeable' knowledge propagation.
mrgFmap :: (MonadUnion bool f, Mergeable bool b, Functor f) => (a -> b) -> f a -> f b
mrgFmap f a = merge $ fmap f a
