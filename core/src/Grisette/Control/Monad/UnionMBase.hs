{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-cse #-}
-- {-# OPTIONS_GHC -fno-full-laziness #-}

module Grisette.Control.Monad.UnionMBase
  ( UnionMBase,
    underlyingUnion,
  )
where

import Data.Functor.Classes
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Grisette.Data.UnionBase
import Data.IORef
import GHC.IO

data UnionMBase bool a where
  UAny :: IORef (Either (UnionBase bool a) (UnionMBase bool a)) -> UnionBase bool a -> UnionMBase bool a
  UMrg :: (Mergeable bool a) => UnionBase bool a -> UnionMBase bool a

freshUAny :: UnionBase bool a -> UnionMBase bool a
freshUAny v = UAny (unsafeDupablePerformIO $ newIORef $ Left v) v
{-# NOINLINE freshUAny #-}

instance (Show a, Show bool) => (Show (UnionMBase bool a)) where
  show (UAny _ u) = "UAny(" ++ show u ++ ")"
  show (UMrg u) = "UMrg(" ++ show u ++ ")"

instance (Show bool) => Show1 (UnionMBase bool) where
  liftShowsPrec sp sl i (UAny _ u) s = "UAny(" ++ liftShowsPrec sp sl i u s ++ ")"
  liftShowsPrec sp sl i (UMrg u) s = "UMrg(" ++ liftShowsPrec sp sl i u s ++ ")"

underlyingUnion :: UnionMBase bool a -> UnionBase bool a
underlyingUnion (UAny _ a) = a
underlyingUnion (UMrg a) = a

instance SymBoolOp bool => UnionOp bool (UnionMBase bool) where
  single v = (freshUAny . single) v
  guard cond (UAny _ a) (UAny _ b) = freshUAny $ guard cond a b
  guard cond (UMrg a) (UAny _ b) = UMrg $ guardWithStrategy mergeStrategy cond a b
  guard cond a (UMrg b) = UMrg $ guardWithStrategy mergeStrategy cond (underlyingUnion a) b
  singleView = singleView . underlyingUnion
  guardView (UAny _ u) = case guardView u of
    Just (c, t, f) -> Just (c, freshUAny t, freshUAny f)
    Nothing -> Nothing
  guardView (UMrg u) = case guardView u of
    Just (c, t, f) -> Just (c, UMrg t, UMrg f)
    Nothing -> Nothing
  leftMost = leftMost . underlyingUnion

instance (SymBoolOp bool) => Functor (UnionMBase bool) where
  fmap f fa = fa >>= return . f

instance (SymBoolOp bool) => Applicative (UnionMBase bool) where
  pure = single
  f <*> a = f >>= (\xf -> a >>= (return . xf))

bindUnion :: SymBoolOp bool => UnionBase bool a -> (a -> UnionMBase bool b) -> UnionMBase bool b
bindUnion (Single a') f' = f' a'
bindUnion (Guard _ cond ifTrue ifFalse) f' =
  guard cond (bindUnion ifTrue f') (bindUnion ifFalse f')

instance (SymBoolOp bool) => Monad (UnionMBase bool) where
  a >>= f = bindUnion (underlyingUnion a) f

instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (UnionMBase bool a) where
  mergeStrategy = SimpleStrategy $ \cond t f -> guard cond t f >>= mrgReturn @bool

instance (SymBoolOp bool, Mergeable bool a) => SimpleMergeable bool (UnionMBase bool a) where
  mrgIf = mrgGuard

instance (SymBoolOp bool) => Mergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => SimpleMergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => UnionMOp bool (UnionMBase bool) where
  merge m@(UMrg _) = m
  merge m@(UAny ref _) = unsafeDupablePerformIO $ atomicModifyIORef' ref $ \case
    x@(Right r) -> (x, r)
    Left _ -> (Right r, r)
      where !r = m >>= mrgSingle
  {-# NOINLINE merge #-}
  mrgSingle = UMrg . single
  mrgGuard cond l r =
    merge $ guard cond l r

instance (SymBoolOp bool, SEq bool a, Mergeable bool bool) => SEq bool (UnionMBase bool a) where
  x ==~ y = case ( do
                     x1 <- x
                     y1 <- y
                     mrgReturn $ x1 ==~ y1
                 ) of
    UMrg (Single v) -> v
    _ -> error "Should not happen"