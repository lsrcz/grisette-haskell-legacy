{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Control.Monad.Union.Mergeable
  ( MergeStrategy (..),
    wrapMergeStrategy,
    guardWithStrategy,
    UnionMOp (..),
    Mergeable (..),
    SimpleMergeable (..),
    Mergeable1 (..),
    SimpleMergeable1 (..),
    StrongSimpleMergeable1 (..),
    withMergeable',
    withSimpleMergeable',
    withStrongSimpleMergeable',
  )
where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Data.Typeable
import Generics.Deriving
import Grisette.Control.Monad.Union.UnionOp
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper

data MergeStrategy bool a where
  SimpleStrategy :: (bool -> a -> a -> a) -> MergeStrategy bool a
  OrderedStrategy :: (Ord idx, Typeable idx) => (a -> idx) -> (idx -> MergeStrategy bool a) -> MergeStrategy bool a
  NoStrategy :: MergeStrategy bool a

wrapMergeStrategy :: MergeStrategy bool a -> (a -> b) -> (b -> a) -> MergeStrategy bool b
wrapMergeStrategy (SimpleStrategy m) wrap unwrap =
  SimpleStrategy
    ( \cond ifTrue ifFalse ->
        wrap $ m cond (unwrap ifTrue) (unwrap ifFalse)
    )
wrapMergeStrategy (OrderedStrategy idxFun substrategy) wrap unwrap =
  OrderedStrategy
    (idxFun . unwrap)
    (\idx -> wrapMergeStrategy (substrategy idx) wrap unwrap)
wrapMergeStrategy NoStrategy _ _ = NoStrategy

guardWithStrategy :: (UnionOp bool u) => MergeStrategy bool a -> bool -> u a -> u a -> u a
guardWithStrategy _ (Conc True) t _ = t
guardWithStrategy _ (Conc False) _ f = f
guardWithStrategy (SimpleStrategy m) cond (SingleU l) (SingleU r) = SingleU $ m cond l r
guardWithStrategy strategy@(OrderedStrategy idxFun substrategy) cond ifTrue ifFalse = case (ifTrue, ifFalse) of
  (SingleU _, SingleU _) -> ssGuard cond ifTrue ifFalse
  (SingleU _, GuardU {}) -> sgGuard cond ifTrue ifFalse
  (GuardU {}, SingleU _) -> gsGuard cond ifTrue ifFalse
  (GuardU {}, GuardU {}) -> ggGuard cond ifTrue ifFalse
  _ -> undefined
  where
    ssGuard cond' ifTrue' ifFalse'
      | idxt < idxf = GuardU cond' ifTrue' ifFalse'
      | idxt == idxf = guardWithStrategy (substrategy idxt) cond' ifTrue' ifFalse'
      | otherwise = GuardU (nots cond') ifFalse' ifTrue'
      where
        idxt = idxFun $ leftMost ifTrue'
        idxf = idxFun $ leftMost ifFalse'
    sgGuard cond' ifTrue' ifFalse'@(GuardU condf ft ff)
      | idxft == idxff = ssGuard cond' ifTrue' ifFalse'
      | idxt < idxft = GuardU cond' ifTrue' ifFalse'
      | idxt == idxft = GuardU (cond' ||~ condf) (guardWithStrategy (substrategy idxt) cond' ifTrue' ft) ff
      | otherwise = GuardU (nots cond' &&~ condf) ft (guardWithStrategy strategy cond' ifTrue' ff)
      where
        idxft = idxFun $ leftMost ft
        idxff = idxFun $ leftMost ff
        idxt = idxFun $ leftMost ifTrue'
    sgGuard _ _ _ = undefined
    gsGuard cond' ifTrue'@(GuardU condt tt tf) ifFalse'
      | idxtt == idxtf = ssGuard cond' ifTrue' ifFalse'
      | idxtt < idxf = GuardU (cond' &&~ condt) ifTrue $ guardWithStrategy strategy cond' tf ifFalse'
      | idxtt == idxf = GuardU (nots cond' ||~ condt) (guardWithStrategy (substrategy idxf) cond' tt ifFalse') tf
      | otherwise = GuardU (nots cond') ifFalse' ifTrue'
      where
        idxtt = idxFun $ leftMost tt
        idxtf = idxFun $ leftMost tf
        idxf = idxFun $ leftMost ifFalse'
    gsGuard _ _ _ = undefined
    ggGuard cond' ifTrue'@(GuardU condt tt tf) ifFalse'@(GuardU condf ft ff)
      | idxtt == idxtf = sgGuard cond' ifTrue' ifFalse'
      | idxft == idxff = gsGuard cond' ifTrue' ifFalse'
      | idxtt < idxft = GuardU (cond' &&~ condt) tt $ guardWithStrategy strategy cond' tf ifFalse'
      | idxtt == idxft =
        let newCond = ites cond' condt condf
            newIfTrue = guardWithStrategy (substrategy idxtt) cond' tt ft
            newIfFalse = guardWithStrategy strategy cond' tf ff
         in GuardU newCond newIfTrue newIfFalse
      | otherwise = GuardU (nots cond' &&~ condf) ft $ guardWithStrategy strategy cond' ifTrue' ff
      where
        idxtt = idxFun $ leftMost tt
        idxtf = idxFun $ leftMost tf
        idxft = idxFun $ leftMost ft
        idxff = idxFun $ leftMost ff
    ggGuard _ _ _ = undefined
guardWithStrategy NoStrategy cond ifTrue ifFalse = GuardU cond ifTrue ifFalse
guardWithStrategy _ _ _ _ = error "Invariant violated"

class Mergeable bool a where
  mergeStrategy :: MergeStrategy bool a
  default mergeStrategy :: (Generic a, Mergeable' bool (Rep a)) => MergeStrategy bool a
  mergeStrategy = wrapMergeStrategy mergeStrategy' to from

class Mergeable bool a => SimpleMergeable bool a where
  merge :: a -> a
  mrgIf :: bool -> a -> a -> a

class UnionOp bool u => UnionMOp bool u | u -> bool where
  mrgSingle :: (Mergeable bool a) => a -> u a
  mrgGuard :: (Mergeable bool a) => bool -> u a -> u a -> u a

class Mergeable1 bool (u :: * -> *) where
  withMergeable :: (Mergeable bool a) => (Mergeable bool (u a) => t) -> t

withMergeable' :: forall bool u a. (Mergeable1 bool u, Mergeable bool a) => (Mergeable bool (u a) => (u a)) -> u a
withMergeable' = withMergeable @bool @u @a

class (Mergeable1 bool u) => SimpleMergeable1 bool u where
  withSimpleMergeable :: (SimpleMergeable bool a) => (SimpleMergeable bool (u a) => t) -> t

class (SimpleMergeable1 bool u) => StrongSimpleMergeable1 bool u | u -> bool where
  withStrongSimpleMergeable :: (Mergeable bool a) => (SimpleMergeable bool (u a) => t) -> t

withSimpleMergeable' ::
  forall bool u a.
  (SimpleMergeable1 bool u, SimpleMergeable bool a) =>
  (SimpleMergeable bool (u a) => (u a)) ->
  u a
withSimpleMergeable' = withSimpleMergeable @bool @u @a

withStrongSimpleMergeable' ::
  forall bool u a.
  (StrongSimpleMergeable1 bool u, Mergeable bool a) =>
  (SimpleMergeable bool (u a) => (u a)) ->
  u a
withStrongSimpleMergeable' = withStrongSimpleMergeable @bool @u @a

-- generic derivation
class Mergeable' bool f where
  mergeStrategy' :: MergeStrategy bool (f a)

instance Mergeable' bool U1 where
  mergeStrategy' = SimpleStrategy (\_ t _ -> t)

instance (Mergeable bool c) => Mergeable' bool (K1 i c) where
  mergeStrategy' = wrapMergeStrategy mergeStrategy K1 unK1

instance (Mergeable' bool a) => Mergeable' bool (M1 i c a) where
  mergeStrategy' = wrapMergeStrategy mergeStrategy' M1 unM1

instance (Mergeable' bool a, Mergeable' bool b) => Mergeable' bool (a :+: b) where
  mergeStrategy' =
    OrderedStrategy
      ( \case
          L1 _ -> False
          R1 _ -> True
      )
      ( \idx ->
          if not idx
            then wrapMergeStrategy mergeStrategy' L1 (\(L1 v) -> v)
            else wrapMergeStrategy mergeStrategy' R1 (\(R1 v) -> v)
      )

wrapMergeStrategy2 ::
  (a -> b -> r) ->
  (r -> (a, b)) ->
  MergeStrategy bool a ->
  MergeStrategy bool b ->
  MergeStrategy bool r
wrapMergeStrategy2 wrap unwrap strategy1 strategy2 =
  case (strategy1, strategy2) of
    (NoStrategy, _) -> NoStrategy
    (_, NoStrategy) -> NoStrategy
    (SimpleStrategy m1, SimpleStrategy m2) ->
      SimpleStrategy $ \cond t f -> case (unwrap t, unwrap f) of
        ((hdt, tlt), (hdf, tlf)) ->
          wrap (m1 cond hdt hdf) (m2 cond tlt tlf)
    (s1@(SimpleStrategy _), OrderedStrategy idxf subf) ->
      OrderedStrategy (idxf . snd . unwrap) (wrapMergeStrategy2 wrap unwrap s1 . subf)
    (OrderedStrategy idxf subf, s2) ->
      OrderedStrategy (idxf . fst . unwrap) (\idx -> wrapMergeStrategy2 wrap unwrap (subf idx) s2)

instance (Mergeable' bool a, Mergeable' bool b) => Mergeable' bool (a :*: b) where
  mergeStrategy' = wrapMergeStrategy2 (:*:) (\(a :*: b) -> (a, b)) mergeStrategy' mergeStrategy'

-- instances

-- Either
instance (SymBoolOp bool, Mergeable bool e, Mergeable bool a) => Mergeable bool (Either e a)

instance (SymBoolOp bool, Mergeable bool e) => Mergeable1 bool (Either e) where
  withMergeable v = v

-- Maybe
instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (Maybe a)

instance (SymBoolOp bool) => Mergeable1 bool Maybe where
  withMergeable v = v

-- (,)
instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable bool (a, b)

instance (SymBoolOp bool, Mergeable bool a) => Mergeable1 bool ((,) a) where
  withMergeable v = v

instance (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b) => SimpleMergeable bool (a, b) where
  merge (a1, b1) = (merge @bool a1, merge @bool b1)
  mrgIf cond (a1, b1) (a2, b2) = (mrgIf cond a1 a2, mrgIf cond b1 b2)

-- (,,)
instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) => Mergeable bool (a, b, c)

instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable1 bool ((,,) a b) where
  withMergeable v = v

instance
  (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b, SimpleMergeable bool c) =>
  SimpleMergeable bool (a, b, c)
  where
  merge (a1, b1, c1) = (merge @bool a1, merge @bool b1, merge @bool c1)
  mrgIf cond (a1, b1, c1) (a2, b2, c2) = (mrgIf cond a1 a2, mrgIf cond b1 b2, mrgIf cond c1 c2)

-- function
instance (SymBoolOp bool, Mergeable bool b) => Mergeable bool (a -> b) where
  mergeStrategy = case mergeStrategy @bool @b of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy

instance (SymBoolOp bool) => Mergeable1 bool ((->) a) where
  withMergeable v = v

instance (SymBoolOp bool, SimpleMergeable bool b) => SimpleMergeable bool (a -> b) where
  merge f = merge @bool . f
  mrgIf cond t f = \v -> mrgIf cond (t v) (f v)

instance (SymBoolOp bool) => SimpleMergeable1 bool ((->) a) where
  withSimpleMergeable v = v

-- MaybeT
deriving instance Generic (MaybeT m a)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) => Mergeable bool (MaybeT m a) where
  mergeStrategy = withMergeable @bool @m @(Maybe a) $ wrapMergeStrategy mergeStrategy MaybeT (\(MaybeT v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Functor m) => Mergeable1 bool (MaybeT m) where
  withMergeable v = v

instance (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable bool a) => SimpleMergeable bool (MaybeT m a) where
  merge (MaybeT v) = withStrongSimpleMergeable @bool @m @(Maybe a) $ MaybeT $ merge @bool v
  mrgIf cond (MaybeT t) (MaybeT f) = withStrongSimpleMergeable @bool @m @(Maybe a) $ MaybeT $ mrgIf @bool cond t f

instance (SymBoolOp bool, StrongSimpleMergeable1 bool m, Functor m) => SimpleMergeable1 bool (MaybeT m) where
  withSimpleMergeable v = v

instance (SymBoolOp bool, StrongSimpleMergeable1 bool m, Functor m) => StrongSimpleMergeable1 bool (MaybeT m) where
  withStrongSimpleMergeable v = v

-- ExceptT
deriving instance (Functor m) => Generic1 (ExceptT e m)

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ExceptT e m a)
  where
  mergeStrategy = withMergeable @bool @m @(Either e a) $ wrapMergeStrategy mergeStrategy ExceptT (\(ExceptT v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ExceptT e m) where
  withMergeable v = v

instance
  (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ExceptT e m a)
  where
  merge (ExceptT v) = withStrongSimpleMergeable @bool @m @(Either e a) $ ExceptT $ merge @bool v
  mrgIf cond (ExceptT t) (ExceptT f) =
    withStrongSimpleMergeable @bool @m @(Either e a) $ ExceptT $ mrgIf @bool cond t f

instance
  (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ExceptT e m)
  where
  withSimpleMergeable v = v

instance
  (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable bool e, Functor m) =>
  StrongSimpleMergeable1 bool (ExceptT e m)
  where
  withStrongSimpleMergeable v = v

-- Coroutine
instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  Mergeable bool (Coroutine sus m a)
  where
  mergeStrategy =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        wrapMergeStrategy mergeStrategy Coroutine (\(Coroutine v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable1 bool sus) => Mergeable1 bool (Coroutine sus m) where
  withMergeable v = v

instance
  (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  SimpleMergeable bool (Coroutine sus m a)
  where
  merge (Coroutine v) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withStrongSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ merge @bool v
  mrgIf cond (Coroutine t) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withStrongSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ mrgIf cond t f

instance
  (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable1 bool sus) =>
  SimpleMergeable1 bool (Coroutine sus m)
  where
  withSimpleMergeable v = v

instance
  (SymBoolOp bool, StrongSimpleMergeable1 bool m, Mergeable1 bool sus) =>
  StrongSimpleMergeable1 bool (Coroutine sus m)
  where
  withStrongSimpleMergeable v = v

deriving instance Generic (Yield x y)

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Yield x y)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Yield x) where
  withMergeable v = v

deriving instance Generic (Await x y)

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Await x y)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Await x) where
  withMergeable v = v

deriving instance Generic (Request req res x)

instance
  (SymBoolOp bool, Mergeable bool req, Mergeable bool res, Mergeable bool x) =>
  Mergeable bool (Request req res x)

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res) => Mergeable1 bool (Request req res) where
  withMergeable v = v

-- state
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @(a, s) $
      withMergeable @bool @((->) s) @(m (a, s)) $
        wrapMergeStrategy mergeStrategy StateT runStateT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (StateT s m) where
  withMergeable v = v

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, StrongSimpleMergeable1 bool m) =>
  SimpleMergeable bool (StateT s m a)
  where
  merge (StateT v) =
    withStrongSimpleMergeable @bool @m @(a, s) $
      withSimpleMergeable @bool @((->) s) @(m (a, s)) $
        StateT $ merge @bool v
  mrgIf cond (StateT t) (StateT f) =
    withStrongSimpleMergeable @bool @m @(a, s) $
      withSimpleMergeable @bool @((->) s) @(m (a, s)) $
        StateT $ mrgIf cond t f

instance
  (SymBoolOp bool, Mergeable bool s, StrongSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (StateT s m)
  where
  withSimpleMergeable v = v

instance
  (SymBoolOp bool, Mergeable bool s, StrongSimpleMergeable1 bool m) =>
  StrongSimpleMergeable1 bool (StateT s m)
  where
  withStrongSimpleMergeable v = v
