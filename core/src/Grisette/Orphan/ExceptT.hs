{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Orphan.ExceptT where

import Grisette.Data.Class.Bool
import Grisette.Control.Monad.Union.Mergeable
import Control.Monad.Except
import Grisette.Control.Monad.Union.MonadUnion
import Grisette.Orphan.Either()
import Grisette.Control.Monad.Union.FunctorMerge
import Grisette.Control.Monad.Union.ApplicativeMerge
import Grisette.Control.Monad.Union.MonadMerge

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e, Mergeable bool a) => Mergeable bool (ExceptT e m a) where
  mergeStrategy = SimpleStrategy $ \cond (ExceptT t) (ExceptT f) -> ExceptT $ mrgIf cond t f

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e) => Mergeable1 bool (ExceptT e m) where

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e) => MergeableContainer bool (ExceptT e m) where
  merge (ExceptT v) = ExceptT $ merge v

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e) => FunctorMerge bool (ExceptT e m) where
  mrgFmap f fa = fa >>= mrgReturn . f

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e) => ApplicativeMerge bool (ExceptT e m) where
  mrgPure = ExceptT . mrgPure . return
  f <*>~ a = f >>= (\xf -> a >>= (mrgReturn . xf))

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e) => MonadMerge bool (ExceptT e m) where
  mrgReturn = mrgPure
  a >>=~ f = a >>= (f >=> mrgReturn)

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool e) => MonadUnion bool (ExceptT e m) where
  mrgIf cond (ExceptT t) (ExceptT f) = ExceptT $ mrgIf cond t f

instance (SymBoolOp bool, SEq bool (m (Either e a))) => SEq bool (ExceptT e m a) where
  (ExceptT a) ==~ (ExceptT b) = a ==~ b

