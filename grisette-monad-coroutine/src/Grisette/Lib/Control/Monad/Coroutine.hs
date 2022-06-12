{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Monad.Coroutine where

import Control.Monad.Coroutine hiding (merge)
import Grisette.Core
import Grisette.Lib.Control.Monad

liftCoroEitherMergeStrategy ::
  (SymBoolOp bool, Mergeable1 bool s, Mergeable1 bool m) =>
  MergeStrategy bool x ->
  MergeStrategy bool (Either (s (Coroutine s m x)) x)
liftCoroEitherMergeStrategy ms =
  liftMergeStrategy2 (liftMergeStrategy (liftMergeStrategy ms)) ms

coroEitherMergeStrategy ::
  (SymBoolOp bool, Mergeable1 bool s, Mergeable1 bool m, Mergeable bool x) =>
  MergeStrategy bool (Either (s (Coroutine s m x)) x)
coroEitherMergeStrategy = liftMergeStrategy2 mergeStrategy1 mergeStrategy

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  Mergeable bool (Coroutine sus m a)
  where
  mergeStrategy =
    wrapMergeStrategy
      (liftMergeStrategy coroEitherMergeStrategy)
      Coroutine
      (\(Coroutine v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable1 bool sus) => Mergeable1 bool (Coroutine sus m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy $ liftCoroEitherMergeStrategy m)
      Coroutine
      (\(Coroutine v) -> v)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a, Mergeable1 bool sus) =>
  SimpleMergeable bool (Coroutine sus m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable1 bool sus) =>
  SimpleMergeable1 bool (Coroutine sus m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable1 bool sus) =>
  UnionLike bool (Coroutine sus m)
  where
  mergeWithStrategy s ((Coroutine v) :: Coroutine sus m a) =
    Coroutine $ mergeWithStrategy (liftCoroEitherMergeStrategy s) v
  mrgIfWithStrategy s cond (Coroutine t) (Coroutine f) =
    Coroutine $ mrgIfWithStrategy (liftCoroEitherMergeStrategy s) cond t f
  single x = Coroutine $ single $ Right x
  unionIf cond (Coroutine t) (Coroutine f) =
    Coroutine $ unionIf cond t f

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
      coroEitherMergeStrategy
      $ return (Left s)
{-# INLINEABLE mrgSuspend #-}

mrgMapMonad ::
  forall s m m' bool x.
  (Functor s, SymBoolOp bool, Mergeable1 bool s, Mergeable bool x, Monad m, MonadUnion bool m') =>
  (forall y. m y -> m' y) ->
  Coroutine s m x ->
  Coroutine s m' x
mrgMapMonad f (Coroutine r) =
  Coroutine
    { resume =
        f r >>= \x ->
          mergeWithStrategy
            coroEitherMergeStrategy
            $ return $ map' x
    }
  where
    map' :: Either (s (Coroutine s m x)) x -> Either (s (Coroutine s m' x)) x
    map' (Right r1) = Right r1
    map' (Left s) = Left $ mrgMapMonad f <$> s
{-# INLINEABLE mrgMapMonad #-}

mrgMapSuspension ::
  forall s m bool x s'.
  (Functor s, SymBoolOp bool, MonadUnion bool m, Mergeable bool x, Mergeable1 bool s') =>
  (forall y. s y -> s' y) ->
  Coroutine s m x ->
  Coroutine s' m x
mrgMapSuspension f (Coroutine r) =
  Coroutine
    { resume =
        r >>= \x ->
          mergeWithStrategy coroEitherMergeStrategy $ return $ map' x
    }
  where
    map' :: Either (s (Coroutine s m x)) x -> Either (s' (Coroutine s' m x)) x
    map' (Right r1) = Right r1
    map' (Left s) = Left $ f $ mrgMapSuspension f <$> s
{-# INLINEABLE mrgMapSuspension #-}

mrgMapFirstSuspension ::
  forall s m bool x.
  (Functor s, SymBoolOp bool, Mergeable1 bool s, MonadUnion bool m, Mergeable bool x) =>
  (forall y. s y -> s y) ->
  Coroutine s m x ->
  Coroutine s m x
mrgMapFirstSuspension f (Coroutine r) =
  Coroutine
    { resume =
        r >>= \s -> mrgReturnWithStrategy coroEitherMergeStrategy $
          case s of
            Right x -> Right x
            Left x -> Left $ f x
    }

instance Mergeable bool (Naught x) where
  mergeStrategy = SimpleStrategy mrgIte

instance Mergeable1 bool Naught where
  liftMergeStrategy _ = SimpleStrategy mrgIte

instance SimpleMergeable bool (Naught x) where
  mrgIte _ x _ = x

instance SimpleMergeable1 bool Naught where
  liftMrgIte _ _ x _ = x

runCoroutine ::
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool x) =>
  Coroutine Naught m x ->
  m x
runCoroutine (Coroutine r) = do
  v <- r
  case v of
    Left _ -> error "Won't happen"
    Right x -> mrgReturn x

mrgBounce ::
  (Functor s, SymBoolOp bool, Mergeable1 bool s, MonadUnion bool m, Mergeable bool x) =>
  (s (Coroutine s m x) -> Coroutine s m x) ->
  Coroutine s m x ->
  Coroutine s m x
mrgBounce f (Coroutine r) = Coroutine $ mergeWithStrategy coroEitherMergeStrategy $ do
  r1 <- r
  case r1 of
    Left s -> resume $ f s
    Right x -> return $ Right x

mrgPogoStick ::
  (MonadUnion bool m, Mergeable bool x) =>
  (s (Coroutine s m x) -> Coroutine s m x) -> Coroutine s m x -> m x
mrgPogoStick f (Coroutine r) = do
  r1 <- r
  case r1 of
    Left h -> mrgPogoStick f $ f h
    Right v -> mrgReturn v

mrgPogoStickM ::
  (MonadUnion bool m, Mergeable bool x) =>
  (s (Coroutine s m x) -> m (Coroutine s m x)) -> Coroutine s m x -> m x
mrgPogoStickM f (Coroutine r) = do
  r1 <- r
  case r1 of
    Left h -> do
      cs <- f h
      mrgPogoStickM f cs
    Right v -> mrgReturn v

mrgFoldRun ::
  (MonadUnion bool m, SymBoolOp bool, Mergeable bool x, Mergeable bool a) =>
  (a -> s (Coroutine s m x) -> (a, Coroutine s m x)) -> a -> Coroutine s m x -> m (a, x)
mrgFoldRun f a (Coroutine r) = do
  r1 <- r
  case r1 of
    Left s -> case f a s of
      (a1, c1) -> mrgFoldRun f a1 c1
    Right v -> mrgReturn (a, v)

type MrgPairBinder bool m =
  forall x y r. (Mergeable bool r) => (x -> y -> m r) -> m x -> m y -> m r

mrgSequentialBinder :: (SymBoolOp bool, MonadUnion bool m) => MrgPairBinder bool m
mrgSequentialBinder f ma mb = merge $ do
  a <- ma
  b <- mb
  f a b
