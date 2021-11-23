{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad.UnionM where

import Data.Functor.Classes
import Grisette.Control.Monad
import Grisette.Control.Monad.Union
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.UnionOp
import Grisette.Data.Class.Bool

data UnionMBase bool a where
  UAny :: UnionBase bool a -> UnionMBase bool a
  UMrg :: (Mergeable bool a) => UnionBase bool a -> UnionMBase bool a

instance (Show a, Show bool) => (Show (UnionMBase bool a)) where
  show (UAny u) = "UAny(" ++ show u ++ ")"
  show (UMrg u) = "UMrg(" ++ show u ++ ")"

instance (Show bool) => Show1 (UnionMBase bool) where
  liftShowsPrec sp sl i (UAny u) s = "UAny(" ++ liftShowsPrec sp sl i u s ++ ")"
  liftShowsPrec sp sl i (UMrg u) s = "UMrg(" ++ liftShowsPrec sp sl i u s ++ ")"

underlyingUnion :: UnionMBase bool a -> UnionBase bool a
underlyingUnion (UAny a) = a
underlyingUnion (UMrg a) = a

instance SymBoolOp bool => UnionOp bool (UnionMBase bool) where
  single = UAny . single
  guard cond (UAny a) (UAny b) = UAny $ guard cond a b
  guard cond (UMrg a) (UAny b) = UMrg $ guardWithStrategy mergeStrategy cond a b
  guard cond a (UMrg b) = UMrg $ guardWithStrategy mergeStrategy cond (underlyingUnion a) b
  singleView = singleView . underlyingUnion
  guardView (UAny u) = case guardView u of
    Just (c, t, f) -> Just (c, UAny t, UAny f)
    Nothing -> Nothing
  guardView (UMrg u) = case guardView u of
    Just (c, t, f) -> Just (c, UMrg t, UMrg f)
    Nothing -> Nothing
  leftMost = leftMost . underlyingUnion

instance SymBoolOp bool => UnionMOp bool (UnionMBase bool) where
  mrgSingle = UMrg . single
  mrgGuard cond l r =
    merge @bool $ guard cond l r

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
  merge u = u >>= mrgSingle
  mrgIf = mrgGuard

instance (SymBoolOp bool) => Mergeable1 bool (UnionMBase bool) where
  withMergeable v = v

instance SymBoolOp bool => SimpleMergeable1 bool (UnionMBase bool) where
  withSimpleMergeable v = v

instance SymBoolOp bool => StrongSimpleMergeable1 bool (UnionMBase bool) where
  withStrongSimpleMergeable v = v

instance (SymBoolOp bool, SEq bool a, Mergeable bool bool) => SEq bool (UnionMBase bool a) where
  x ==~ y = case ( do
                     x1 <- x
                     y1 <- y
                     mrgReturn @bool $ x1 ==~ y1
                 ) of
    UMrg (Single v) -> v
    _ -> error "Should not happen"