{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Lib.Control.Monad.Coroutine.SuspensionFunctors where

import Control.Monad.Coroutine.SuspensionFunctors
import Grisette.Core
import Control.Monad.Coroutine
import Grisette.Lib.Control.Monad.Coroutine
import Grisette.Lib.Control.Monad

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Yield x y) where
  mergingStrategy = product2Strategy Yield (\(Yield x y) -> (x, y)) mergingStrategy mergingStrategy

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Yield x) where
  liftMergingStrategy = product2Strategy Yield (\(Yield x y) -> (x, y)) mergingStrategy

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Await x y) where
  mergingStrategy = wrapStrategy mergingStrategy Await (\(Await x) -> x)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Await x) where
  liftMergingStrategy m = wrapStrategy (liftMergingStrategy m) Await (\(Await x) -> x)

instance
  (SymBoolOp bool, Mergeable bool req, Mergeable bool res, Mergeable bool x) =>
  Mergeable bool (Request req res x)
  where
  mergingStrategy = product2Strategy Request (\(Request x y) -> (x, y)) mergingStrategy mergingStrategy

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res) => Mergeable1 bool (Request req res) where
  liftMergingStrategy m = product2Strategy Request (\(Request x y) -> (x, y)) mergingStrategy (liftMergingStrategy m)

mrgYield :: (SymBoolOp bool, MonadUnion bool m, Mergeable bool x) => x -> Coroutine (Yield x) m ()
mrgYield x = mrgSuspend (Yield x $ mrgReturn ())
{-# INLINEABLE mrgYield #-}

mrgAwait :: (SymBoolOp bool, MonadUnion bool m, Mergeable bool x) => Coroutine (Await x) m x
mrgAwait = mrgSuspend (Await mrgReturn)
{-# INLINEABLE mrgAwait #-}

mrgRequest :: (SymBoolOp bool, MonadUnion bool m, Mergeable bool x, Mergeable bool y) => x -> Coroutine (Request x y) m y
mrgRequest x = mrgSuspend (Request x mrgReturn)
{-# INLINEABLE mrgRequest #-}
