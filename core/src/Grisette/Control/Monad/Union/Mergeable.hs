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
{-# LANGUAGE QuantifiedConstraints #-}
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
    -- UnionMOp (..),
    withMergeable,
    withSimpleMergeable,
    withUnionMSimpleMergeable,
    withSimpleMergeableU,
    withUnionMSimpleMergeableU,
  )
where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import Data.Constraint
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

class Mergeable bool a => SimpleMergeable bool a | a -> bool where
  mrgIf :: bool -> a -> a -> a

class Mergeable1 bool (u :: * -> *) where
  withMergeableT :: forall a t. (Mergeable bool a) => (Mergeable bool (u a) => t a) -> t a
  default withMergeableT ::
    (forall b. Mergeable bool b => Mergeable bool (u b)) =>
    forall a t.
    (Mergeable bool a) =>
    (Mergeable bool (u a) => t a) ->
    t a
  withMergeableT v = v

data CConst (c :: Constraint) a b = c => CConst {unCConst :: a}

withMergeable :: forall bool u a b. (Mergeable1 bool u, Mergeable bool a) => (Mergeable bool (u a) => b) -> b
withMergeable v = unCConst $ withMergeableT @bool @u @a @(CConst (Mergeable bool (u a)) b) $ CConst v

class (Mergeable1 bool u) => SimpleMergeable1 bool u where
  withSimpleMergeableT :: forall a t. (SimpleMergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withSimpleMergeableT ::
    (forall b. SimpleMergeable bool b => SimpleMergeable bool (u b)) =>
    forall a t.
    (SimpleMergeable bool a) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withSimpleMergeableT v = v

withSimpleMergeable :: forall bool u a b. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withSimpleMergeable v = unCConst $ withSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

withSimpleMergeableU :: forall bool u a. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withSimpleMergeableU = withSimpleMergeable @bool @u @a

class (SimpleMergeable1 bool u) => UnionMOp bool u | u -> bool where
  withUnionMSimpleMergeableT :: forall a t. (Mergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withUnionMSimpleMergeableT ::
    (forall b. Mergeable bool b => SimpleMergeable bool (u b)) =>
    (Mergeable bool a, SimpleMergeable bool (u a)) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withUnionMSimpleMergeableT v = v
  merge :: (Mergeable bool a) => u a -> u a
  mrgSingle :: (Mergeable bool a) => a -> u a
  mrgGuard :: (Mergeable bool a) => bool -> u a -> u a -> u a

withUnionMSimpleMergeable :: forall bool u a b. (UnionMOp bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withUnionMSimpleMergeable v = unCConst $ withUnionMSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

withUnionMSimpleMergeableU :: forall bool u a. (UnionMOp bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withUnionMSimpleMergeableU = withUnionMSimpleMergeable @bool @u @a

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

instance (SymBoolOp bool, Mergeable bool e) => Mergeable1 bool (Either e)

-- Maybe
instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (Maybe a)

instance (SymBoolOp bool) => Mergeable1 bool Maybe

-- (,)
instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable bool (a, b)

instance (SymBoolOp bool, Mergeable bool a) => Mergeable1 bool ((,) a)

instance (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b) => SimpleMergeable bool (a, b) where
  mrgIf cond (a1, b1) (a2, b2) = (mrgIf cond a1 a2, mrgIf cond b1 b2)

-- (,,)
instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) => Mergeable bool (a, b, c)

instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable1 bool ((,,) a b)

instance
  (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b, SimpleMergeable bool c) =>
  SimpleMergeable bool (a, b, c)
  where
  mrgIf cond (a1, b1, c1) (a2, b2, c2) = (mrgIf cond a1 a2, mrgIf cond b1 b2, mrgIf cond c1 c2)

-- function
instance (SymBoolOp bool, Mergeable bool b) => Mergeable bool (a -> b) where
  mergeStrategy = case mergeStrategy @bool @b of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy

instance (SymBoolOp bool) => Mergeable1 bool ((->) a)

instance (SymBoolOp bool, SimpleMergeable bool b) => SimpleMergeable bool (a -> b) where
  mrgIf cond t f = \v -> mrgIf cond (t v) (f v)

instance (SymBoolOp bool) => SimpleMergeable1 bool ((->) a) where

-- MaybeT
deriving instance Generic (MaybeT m a)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) => Mergeable bool (MaybeT m a) where
  mergeStrategy = withMergeable @bool @m @(Maybe a) $ wrapMergeStrategy mergeStrategy MaybeT runMaybeT

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (MaybeT m)

instance (SymBoolOp bool, UnionMOp bool m, Mergeable bool a) => SimpleMergeable bool (MaybeT m a) where
  mrgIf = mrgGuard

instance (SymBoolOp bool, UnionMOp bool m) => SimpleMergeable1 bool (MaybeT m) where

instance (SymBoolOp bool, UnionMOp bool m) => UnionMOp bool (MaybeT m) where
  merge (MaybeT v) = MaybeT $ merge @bool v
  mrgSingle v = MaybeT $ mrgSingle $ return v
  mrgGuard cond (MaybeT t) (MaybeT f) = MaybeT $ mrgGuard cond t f

-- ExceptT
deriving instance (Functor m) => Generic1 (ExceptT e m)

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ExceptT e m a)
  where
  mergeStrategy = withMergeable @bool @m @(Either e a) $ wrapMergeStrategy mergeStrategy ExceptT runExceptT

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ExceptT e m)

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ExceptT e m a)
  where
  mrgIf cond (ExceptT t) (ExceptT f) =
    withUnionMSimpleMergeable @bool @m @(Either e a) $ ExceptT $ mrgIf cond t f

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ExceptT e m)
  where

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Functor m) =>
  UnionMOp bool (ExceptT e m)
  where
  merge (ExceptT v) = ExceptT $ merge v
  mrgSingle v = ExceptT $ mrgSingle $ return v
  mrgGuard cond (ExceptT t) (ExceptT f) = ExceptT $ mrgGuard cond t f

-- Coroutine
deriving instance Generic (Coroutine sus m a)
instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  Mergeable bool (Coroutine sus m a)
  where
  mergeStrategy =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        wrapMergeStrategy mergeStrategy Coroutine (\(Coroutine v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable1 bool sus) => Mergeable1 bool (Coroutine sus m)

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable bool a, Mergeable1 bool sus) =>
  SimpleMergeable bool (Coroutine sus m a)
  where
  mrgIf cond (Coroutine t) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withUnionMSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ mrgIf cond t f

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable1 bool sus) =>
  SimpleMergeable1 bool (Coroutine sus m)
  where

instance
  (SymBoolOp bool, UnionMOp bool m, Mergeable1 bool sus) =>
  UnionMOp bool (Coroutine sus m)
  where
  merge ((Coroutine v) :: Coroutine sus m a) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withUnionMSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ merge @bool v
  mrgSingle (v :: a) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ mrgSingle $ return v
  mrgGuard cond ((Coroutine t) :: Coroutine sus m a) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      Coroutine $ mrgGuard cond t f

deriving instance Generic (Yield x y)

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Yield x y)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Yield x)

deriving instance Generic (Await x y)

instance (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Await x y)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Await x)

deriving instance Generic (Request req res x)

instance
  (SymBoolOp bool, Mergeable bool req, Mergeable bool res, Mergeable bool x) =>
  Mergeable bool (Request req res x)

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res) => Mergeable1 bool (Request req res)

-- state
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @(a, s) $
      withMergeable @bool @((->) s) @(m (a, s)) $
        wrapMergeStrategy mergeStrategy StateT runStateT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (StateT s m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionMOp bool m) =>
  SimpleMergeable bool (StateT s m a)
  where
  mrgIf cond (StateT t) (StateT f) =
    withUnionMSimpleMergeable @bool @m @(a, s) $
      withSimpleMergeable @bool @((->) s) @(m (a, s)) $
        StateT $ mrgIf cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionMOp bool m) =>
  SimpleMergeable1 bool (StateT s m)
  where

instance
  (SymBoolOp bool, Mergeable bool s, UnionMOp bool m) =>
  UnionMOp bool (StateT s m)
  where
  merge (StateT f) = StateT $ \v -> merge $ f v
  mrgSingle v = StateT $ \s -> mrgSingle (v, s)
  mrgGuard cond (StateT t) (StateT f) = StateT $ \s -> mrgGuard cond (t s) (f s)
