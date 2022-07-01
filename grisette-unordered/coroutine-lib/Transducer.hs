module Transducer where

import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Data.Functor.Sum
import Grisette
import Grisette.Lib.MonadCoroutine

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
