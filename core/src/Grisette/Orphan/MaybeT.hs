{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Orphan.MaybeT where

import Control.Monad.Trans.Maybe
import Grisette.Data.Class.Bool
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.MonadUnion
import Grisette.Orphan.Maybe()
import Grisette.Control.Monad.Union.FunctorMerge
import Grisette.Control.Monad.Union.ApplicativeMerge
import Grisette.Control.Monad.Union.MonadMerge
import Control.Monad

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool a) => Mergeable bool (MaybeT m a) where
  mergeStrategy = SimpleStrategy $ \cond (MaybeT t) (MaybeT f) -> MaybeT $ mrgIf cond t f

instance (SymBoolOp bool, MonadUnion bool m) => Mergeable1 bool (MaybeT m) where
  mergeStrategy1 = mergeStrategy

instance (SymBoolOp bool, MonadUnion bool m) => MergeableContainer bool (MaybeT m) where
  merge (MaybeT v) = MaybeT $ merge v

instance (SymBoolOp bool, MonadUnion bool m) => FunctorMerge bool (MaybeT m) where
  mrgFmap f fa = fa >>= mrgReturn . f

instance (SymBoolOp bool, MonadUnion bool m) => ApplicativeMerge bool (MaybeT m) where
  mrgPure = MaybeT . mrgPure . return
  f <*>~ a = f >>= (\xf -> a >>= (mrgReturn . xf))

instance (SymBoolOp bool, MonadUnion bool m) => MonadMerge bool (MaybeT m) where
  mrgReturn = mrgPure
  a >>=~ f = a >>= (f >=> mrgReturn)

instance (SymBoolOp bool, MonadUnion bool m) => MonadUnion bool (MaybeT m) where
  mrgIf cond (MaybeT t) (MaybeT f) = MaybeT $ mrgIf cond t f

instance (SymBoolOp bool, SEq bool (m (Maybe a))) => SEq bool (MaybeT m a) where
  (MaybeT a) ==~ (MaybeT b) = a ==~ b


