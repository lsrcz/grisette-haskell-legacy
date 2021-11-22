{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
module Grisette.Orphan.Coroutine where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.MonadUnion
import Grisette.Data.Class.Bool
import Grisette.Orphan.Either
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.FunctorMerge
import Grisette.Control.Monad.Union.ApplicativeMerge
import Grisette.Control.Monad.Union.MonadMerge
import Control.Monad
import GHC.Generics
import Grisette.Orphan.Function

instance (SymBoolOp bool, MonadUnion bool m, Mergeable bool a, Mergeable1 bool sus) => Mergeable bool (Coroutine sus m a) where
  mergeStrategy = SimpleStrategy $ \cond (Coroutine t) (Coroutine f) -> Coroutine $ mrgIf cond t f

instance (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus) => Mergeable1 bool (Coroutine sus m) where

instance (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus) => MergeableContainer bool (Coroutine sus m) where
  merge (Coroutine v) = Coroutine $ merge v

instance (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus, Functor sus) => FunctorMerge bool (Coroutine sus m) where
  mrgFmap f fa = fa >>= mrgReturn . f

instance (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus, Functor sus) => ApplicativeMerge bool (Coroutine sus m) where
  mrgPure = Coroutine . mrgPure . return
  f <*>~ a = f >>= (\xf -> a >>= mrgReturn . xf)

instance (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus, Functor sus) => MonadMerge bool (Coroutine sus m) where
  mrgReturn = mrgPure
  a >>=~ f = a >>= (f >=> mrgReturn)

instance (SymBoolOp bool, MonadUnion bool m, Mergeable1 bool sus, Functor sus) => MonadUnion bool (Coroutine sus m) where
  mrgIf cond (Coroutine t) (Coroutine f) = Coroutine $ mrgIf cond t f

deriving instance Generic (Yield x y)

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Yield x y) where

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Yield x) where

deriving instance Generic (Await x y)

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Await x y) where

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Await x) where

deriving instance Generic (Request req res x)

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res, Mergeable bool x) => Mergeable bool (Request req res x) where

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res) => Mergeable1 bool (Request req res) where


