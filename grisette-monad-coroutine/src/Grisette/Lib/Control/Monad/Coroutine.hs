{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE RankNTypes #-}

module Grisette.Lib.Control.Monad.Coroutine where

import Control.Monad.Coroutine hiding (merge)
import Grisette.Core

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  Mergeable bool (Coroutine sus m a)
  where
  mergeStrategy =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy2 mergeStrategy1 mergeStrategy))
      Coroutine
      (\(Coroutine v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable1 bool sus) => Mergeable1 bool (Coroutine sus m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy2 (liftMergeStrategy (liftMergeStrategy m)) m))
      Coroutine
      (\(Coroutine v) -> v)

instance
  (SymBoolOp bool, UnionMergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  SimpleMergeable bool (Coroutine sus m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, UnionMergeable1 bool m, Mergeable1 bool sus) =>
  SimpleMergeable1 bool (Coroutine sus m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionMergeable1 bool m, Mergeable1 bool sus) =>
  UnionMergeable1 bool (Coroutine sus m)
  where
  mergeWithStrategy s ((Coroutine v) :: Coroutine sus m a) =
    Coroutine $ mergeWithStrategy (liftMergeStrategy2 (liftMergeStrategy (liftMergeStrategy s)) s) v
  mrgIfWithStrategy s cond (Coroutine t) (Coroutine f) =
    Coroutine $ mrgIfWithStrategy (liftMergeStrategy2 (liftMergeStrategy (liftMergeStrategy s)) s) cond t f

instance
  (Monoid symbolSet, ExtractSymbolics symbolSet (m (Either (sus (Coroutine sus m a)) a))) =>
  ExtractSymbolics symbolSet (Coroutine sus m a)
  where
  extractSymbolics (Coroutine v) = extractSymbolics v

mrgSuspend ::
  forall m s bool x.
  (Functor s, MonadUnion bool m, SymBoolOp bool, Mergeable bool x, Mergeable1 bool s) =>
  s (Coroutine s m x) ->
  Coroutine s m x
mrgSuspend s =
  Coroutine $
    mergeWithStrategy
      (liftMergeStrategy2 mergeStrategy1 mergeStrategy) $
      return (Left s)
{-# INLINEABLE mrgSuspend #-}

mrgMapSuspension ::
  forall s m bool x s'.
  (Functor s, SymBoolOp bool, MonadUnion bool m, Mergeable bool x, Mergeable1 bool s') =>
  (forall y. s y -> s' y) ->
  Coroutine s m x ->
  Coroutine s' m x
mrgMapSuspension f cort = Coroutine {resume = resume cort >>= \x ->
  mergeWithStrategy (liftMergeStrategy2 mergeStrategy1 mergeStrategy) $ return $ map' x}
  where
    map' :: Either (s (Coroutine s m x)) x -> Either (s' (Coroutine s' m x)) x
    map' (Right r1) = Right r1
    map' (Left s) = Left $ f $ mrgMapSuspension f <$> s
{-# INLINEABLE mrgMapSuspension #-}

