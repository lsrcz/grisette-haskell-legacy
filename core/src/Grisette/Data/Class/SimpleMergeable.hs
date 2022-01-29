{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Grisette.Data.Class.SimpleMergeable
  ( UnionMOp (..),
    getSingle,
    SimpleMergeable (..),
    SimpleMergeable1 (..),
    withSimpleMergeable,
    withUnionMSimpleMergeable,
    withSimpleMergeableU,
    withUnionMSimpleMergeableU,
  )
where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.Utils.CConst
import Grisette.Data.Class.UnionOp
import GHC.Generics

class SimpleMergeable' bool f where
  mrgIf' :: bool -> f a -> f a -> f a

instance (SimpleMergeable' bool U1) where
  mrgIf' = \_ t _ -> t

instance (SimpleMergeable' bool V1) where
  mrgIf' = \_ t _ -> t

instance (SimpleMergeable bool c) => (SimpleMergeable' bool (K1 i c)) where
  mrgIf' = \cond (K1 a) (K1 b) -> K1 $ mrgIf cond a b

instance (SimpleMergeable' bool a) => (SimpleMergeable' bool (M1 i c a)) where
  mrgIf' = \cond (M1 a) (M1 b) -> M1 $ mrgIf' cond a b

instance (SimpleMergeable' bool a, SimpleMergeable' bool b) => (SimpleMergeable' bool (a :*: b)) where
  mrgIf' = \cond (a1 :*: a2) (b1 :*: b2) -> mrgIf' cond a1 b1 :*: mrgIf' cond a2 b2

class Mergeable bool a => SimpleMergeable bool a where
  mrgIf :: bool -> a -> a -> a
  default mrgIf :: (Generic a, SimpleMergeable' bool (Rep a)) => bool -> a -> a -> a
  mrgIf cond t f = to $ mrgIf' cond (from t) (from f)

getSingle :: forall bool u a. (SimpleMergeable bool a, UnionMOp bool u, UnionOp bool u) => u a -> a
getSingle u = case merge u of
  SingleU x -> x
  _ -> error "Should not happen"

class (Mergeable1 bool u) => SimpleMergeable1 bool u where
  withSimpleMergeableT :: forall a t. (SimpleMergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withSimpleMergeableT ::
    (forall b. SimpleMergeable bool b => SimpleMergeable bool (u b)) =>
    forall a t.
    (SimpleMergeable bool a) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withSimpleMergeableT v = v

withSimpleMergeable :: forall bool u a b. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withSimpleMergeable v = unCConst $ withSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

withSimpleMergeableU :: forall bool u a. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withSimpleMergeableU = withSimpleMergeable @bool @u @a

class (SimpleMergeable1 bool u) => UnionMOp bool u | u -> bool where
  withUnionMSimpleMergeableT :: forall a t. (Mergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withUnionMSimpleMergeableT ::
    (forall b. Mergeable bool b => SimpleMergeable bool (u b)) =>
    (Mergeable bool a, SimpleMergeable bool (u a)) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withUnionMSimpleMergeableT v = v
  merge :: (Mergeable bool a) => u a -> u a
  mrgSingle :: (Mergeable bool a) => a -> u a
  mrgGuard :: (Mergeable bool a) => bool -> u a -> u a -> u a

withUnionMSimpleMergeable :: forall bool u a b. (UnionMOp bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withUnionMSimpleMergeable v = unCConst $ withUnionMSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

withUnionMSimpleMergeableU :: forall bool u a. (UnionMOp bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withUnionMSimpleMergeableU = withUnionMSimpleMergeable @bool @u @a

instance (SymBoolOp bool) => SimpleMergeable bool () where
  mrgIf _ t _ = t

instance (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b) => SimpleMergeable bool (a, b) where
  mrgIf cond (a1, b1) (a2, b2) = (mrgIf cond a1 a2, mrgIf cond b1 b2)

instance
  (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b, SimpleMergeable bool c) =>
  SimpleMergeable bool (a, b, c)
  where
  mrgIf cond (a1, b1, c1) (a2, b2, c2) = (mrgIf cond a1 a2, mrgIf cond b1 b2, mrgIf cond c1 c2)

instance (SymBoolOp bool, SimpleMergeable bool b) => SimpleMergeable bool (a -> b) where
  mrgIf cond t f = \v -> mrgIf cond (t v) (f v)

instance (SymBoolOp bool) => SimpleMergeable1 bool ((->) a)

instance (SymBoolOp bool, UnionMOp bool m, Mergeable bool a) => SimpleMergeable bool (MaybeT m a) where
  mrgIf = mrgGuard

instance (SymBoolOp bool, UnionMOp bool m) => SimpleMergeable1 bool (MaybeT m)

instance (SymBoolOp bool, UnionMOp bool m) => UnionMOp bool (MaybeT m) where
  merge (MaybeT v) = MaybeT $ merge @bool v
  mrgSingle v = MaybeT $ mrgSingle $ return v
  mrgGuard cond (MaybeT t) (MaybeT f) = MaybeT $ mrgGuard cond t f

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ExceptT e m a)
  where
  mrgIf cond (ExceptT t) (ExceptT f) =
    withUnionMSimpleMergeable @bool @m @(Either e a) $ ExceptT $ mrgIf cond t f

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ExceptT e m)

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Functor m) =>
  UnionMOp bool (ExceptT e m)
  where
  merge (ExceptT v) = ExceptT $ merge v
  mrgSingle v = ExceptT $ mrgSingle $ return v
  mrgGuard cond (ExceptT t) (ExceptT f) = ExceptT $ mrgGuard cond t f

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool a, Mergeable1 bool sus) =>
  SimpleMergeable bool (Coroutine sus m a)
  where
  mrgIf cond (Coroutine t) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withUnionMSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ mrgIf cond t f

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable1 bool sus) =>
  SimpleMergeable1 bool (Coroutine sus m)

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable1 bool sus) =>
  UnionMOp bool (Coroutine sus m)
  where
  merge ((Coroutine v) :: Coroutine sus m a) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withUnionMSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ merge @bool v
  mrgSingle (v :: a) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ mrgSingle $ return v
  mrgGuard cond ((Coroutine t) :: Coroutine sus m a) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ mrgGuard cond t f

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionMOp bool m) =>
  SimpleMergeable bool (StateT s m a)
  where
  mrgIf cond (StateT t) (StateT f) =
    withUnionMSimpleMergeable @bool @m @(a, s) $
      withSimpleMergeable @bool @((->) s) @(m (a, s)) $
        StateT $ mrgIf cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionMOp bool m) =>
  SimpleMergeable1 bool (StateT s m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionMOp bool m) =>
  UnionMOp bool (StateT s m)
  where
  merge (StateT f) = StateT $ \v -> merge $ f v
  mrgSingle v = StateT $ \s -> mrgSingle (v, s)
  mrgGuard cond (StateT t) (StateT f) = StateT $ \s -> mrgGuard cond (t s) (f s)
