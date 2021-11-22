{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Control.Monad.Union.Mergeable where

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

class Mergeable bool a | a -> bool where
  mergeStrategy :: MergeStrategy bool a
  default mergeStrategy :: (Generic a, Mergeable' bool (Rep a)) => MergeStrategy bool a
  mergeStrategy = wrapMergeStrategy mergeStrategy' to from

class UnionOp bool u => UnionMOp bool u | u -> bool where
  mrgSingle :: (Mergeable bool a) => a -> u a
  mrgGuard :: (Mergeable bool a) => bool -> u a -> u a -> u a

class Mergeable1 bool u | u -> bool where
  mergeStrategy1 :: (Mergeable bool a) => MergeStrategy bool (u a)
  default mergeStrategy1 :: (Mergeable bool (u a)) => MergeStrategy bool (u a)
  mergeStrategy1 = mergeStrategy

class (Mergeable1 bool u) => MergeableContainer bool u | u -> bool where
  merge :: (Mergeable bool a) => u a -> u a

class Mergeable' bool f where
  mergeStrategy' :: MergeStrategy bool (f a)

instance Mergeable' bool U1 where
  mergeStrategy' = SimpleStrategy (\_ t _ -> t)

instance (Mergeable bool c) => Mergeable' bool (K1 i c) where
  mergeStrategy' = case mergeStrategy of
    SimpleStrategy m -> SimpleStrategy $ \cond (K1 t) (K1 f) -> K1 $ m cond t f
    OrderedStrategy fcidx f -> OrderedStrategy (\(K1 v) -> fcidx v) (\idx -> wrapMergeStrategy (f idx) K1 (\(K1 v) -> v))
    NoStrategy -> NoStrategy

instance (Mergeable' bool a) => Mergeable' bool (M1 i c a) where
  mergeStrategy' = case mergeStrategy' of
    SimpleStrategy m -> SimpleStrategy $ \cond (M1 t) (M1 f) -> M1 $ m cond t f
    OrderedStrategy fcidx f -> OrderedStrategy (\(M1 v) -> fcidx v) (\idx -> wrapMergeStrategy (f idx) M1 (\(M1 v) -> v))
    NoStrategy -> NoStrategy

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

wrapMergeStrategy2 :: (a -> b -> r) -> (r -> (a, b)) -> MergeStrategy bool a -> MergeStrategy bool b -> MergeStrategy bool r
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
