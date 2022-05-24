{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Lib.Control.Monad.Coroutine.SuspensionFunctors where

import Control.Monad.Coroutine.SuspensionFunctors
import Grisette.Core
import Control.Monad.Coroutine
import Data.Functor.Sum
import Grisette.Lib.Control.Monad.Coroutine

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Yield x y) where
  mergeStrategy = wrapMergeStrategy2 Yield (\(Yield x y) -> (x, y)) mergeStrategy mergeStrategy

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Yield x) where
  liftMergeStrategy = wrapMergeStrategy2 Yield (\(Yield x y) -> (x, y)) mergeStrategy

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Await x y) where
  mergeStrategy = wrapMergeStrategy mergeStrategy Await (\(Await x) -> x)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Await x) where
  liftMergeStrategy m = wrapMergeStrategy (liftMergeStrategy m) Await (\(Await x) -> x)

instance
  (SymBoolOp bool, Mergeable bool req, Mergeable bool res, Mergeable bool x) =>
  Mergeable bool (Request req res x)
  where
  mergeStrategy = wrapMergeStrategy2 Request (\(Request x y) -> (x, y)) mergeStrategy mergeStrategy

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res) => Mergeable1 bool (Request req res) where
  liftMergeStrategy m = wrapMergeStrategy2 Request (\(Request x y) -> (x, y)) mergeStrategy (liftMergeStrategy m)

mrgYield :: (SymBoolOp bool, MonadUnion bool m, Mergeable bool x) => x -> Coroutine (Yield x) m ()
mrgYield x = mrgSuspend (Yield x $ mrgReturn ())
{-# INLINEABLE mrgYield #-}

simpleTransducer ::
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool a, Mergeable bool x) =>
  (a -> Coroutine (Yield x) m ()) ->
  Coroutine (Sum (Await a) (Yield x)) m ()
simpleTransducer f = mrgSuspend (InL $ Await $ \x -> mapSuspension InR (f x) >> simpleTransducer f)
{-# INLINEABLE simpleTransducer #-}

mrgWeaveYieldTransducer ::
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool b) =>
  WeaveStepper (Yield a) (Sum (Await a) (Yield b)) (Yield b) m () () ()
mrgWeaveYieldTransducer _ _ (Right ()) = mrgReturn ()
mrgWeaveYieldTransducer w (Left l) (Left (InR (Yield y c1))) = mrgSuspend (Yield y $ w (suspend l) c1)
mrgWeaveYieldTransducer w (Left (Yield x c)) (Left (InL (Await f))) = w c $ f x
mrgWeaveYieldTransducer _ (Right ()) (Left (InL (Await _))) = mrgReturn ()
mrgWeaveYieldTransducer w (Right ()) (Left (InR (Yield y c1))) = mrgSuspend (Yield y $ w (return ()) c1)
{-# INLINEABLE mrgWeaveYieldTransducer #-}

(|->) ::
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool x) =>
  Coroutine (Yield a) m () ->
  Coroutine (Sum (Await a) (Yield x)) m () ->
  Coroutine (Yield x) m ()
(|->) = weave sequentialBinder mrgWeaveYieldTransducer
{-# INLINEABLE (|->) #-}

infixl 1 |->

(|>>=) ::
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool a, Mergeable bool x) =>
  Coroutine (Yield a) m () ->
  (a -> Coroutine (Yield x) m ()) ->
  Coroutine (Yield x) m ()
(|>>=) l f = l |-> simpleTransducer f
{-# INLINEABLE (|>>=) #-}

