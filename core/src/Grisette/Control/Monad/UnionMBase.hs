{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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
  merge u = u >>= mrgSingle
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