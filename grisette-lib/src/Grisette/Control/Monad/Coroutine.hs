{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
module Grisette.Control.Monad.Coroutine
  ( mrgSuspend,
    mrgYield,
    mrgMapSuspension,
    simpleTransducer,
    mrgWeaveYieldTransducer,
    (|->),
    (|>>=),
  )
where

import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Data.Functor.Sum
import Grisette.Control.Monad
import Grisette.Control.Monad.Union
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable

mrgSuspend ::
  forall m s bool x.
  (Functor s, MonadUnion bool m, SymBoolOp bool, Mergeable bool x, Mergeable1 bool s) =>
  s (Coroutine s m x) ->
  Coroutine s m x
mrgSuspend s = withMergeable @bool @s @(Coroutine s m x) $ Coroutine $ mrgReturn @bool (Left s)
{-# INLINEABLE mrgSuspend #-}

mrgYield :: (SymBoolOp bool, MonadUnion bool m, Mergeable bool x) => x -> Coroutine (Yield x) m ()
mrgYield x = mrgSuspend (Yield x $ mrgReturn ())
{-# INLINEABLE mrgYield #-}

mrgMapSuspension ::
  forall s m bool x s'.
  (Functor s, SymBoolOp bool, MonadUnion bool m, Mergeable bool x, Mergeable1 bool s') =>
  (forall y. s y -> s' y) ->
  Coroutine s m x ->
  Coroutine s' m x
mrgMapSuspension f cort = withMergeable @bool @s' @(Coroutine s' m x) Coroutine {resume = mrgFmap map' $ resume cort}
  where
    map' :: Either (s (Coroutine s m x)) x -> Either (s' (Coroutine s' m x)) x
    map' (Right r1) = Right r1
    map' (Left s) = Left $ f $ mrgMapSuspension f <$> s
{-# INLINEABLE mrgMapSuspension #-}

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