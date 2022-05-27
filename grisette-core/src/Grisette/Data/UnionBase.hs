{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Grisette.Data.UnionBase
  ( UnionBase (..),
    guardWithLeftMost,
    guardWithStrategy,
    fullReconstruct,
  )
where

import Control.DeepSeq
import Data.Functor.Classes
import Data.Hashable
import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.UnionOp
import Language.Haskell.TH.Syntax

-- | The default union implementation.
data UnionBase b a
  = Single a              -- ^ A single value
  | Guard                 -- ^ A guard value
      a                   -- ^ Cached leftmost value
      !Bool               -- ^ Is merged invariant already maintained?
      !b                  -- ^ Guard condition
      (UnionBase b a)     -- ^ True branch
      (UnionBase b a)     -- ^ False branch
  deriving (Generic, Eq, Lift, Generic1)

instance (Eq b) => Eq1 (UnionBase b) where
  liftEq e (Single a) (Single b) = e a b
  liftEq e (Guard l1 i1 c1 t1 f1) (Guard l2 i2 c2 t2 f2) =
    e l1 l2 && i1 == i2 && c1 == c2 && liftEq e t1 t2 && liftEq e f1 f2
  liftEq _ _ _ = False 
instance (NFData b, NFData a) => NFData (UnionBase b a) where
  rnf = rnf1

instance (NFData b) => NFData1 (UnionBase b) where
  liftRnf = liftRnf2 rnf

instance NFData2 UnionBase where
  liftRnf2 _b _a (Single a) = _a a
  liftRnf2 _b _a (Guard a bo b l r) = _a a `seq` rnf bo `seq` _b b `seq` liftRnf2 _b _a l `seq` liftRnf2 _b _a r

-- | Build 'Guard' with leftmost cache correctly maintained.
--
-- Usually you should never directly try to build a 'Guard' with its constructor.
guardWithLeftMost :: (SymBoolOp b) => Bool -> b -> UnionBase b a -> UnionBase b a -> UnionBase b a
guardWithLeftMost inv cond t = Guard (leftMost t) inv cond t

instance SymBoolOp bool => UnionOp bool (UnionBase bool) where
  single = Single
  guard = guardWithLeftMost False
  singleView (Single a) = Just a
  singleView _ = Nothing
  guardView (Guard _ _ cond ifTrue ifFalse) = Just (cond, ifTrue, ifFalse)
  guardView _ = Nothing
  leftMost (Single a) = a
  leftMost (Guard a _ _ _ _) = a

instance (Show b) => Show1 (UnionBase b) where
  liftShowsPrec sp _ i (Single a) = showsUnaryWith sp "Single" i a
  liftShowsPrec sp sl i (Guard _ _ cond t f) =
    showParen (i > 10) $
      showString "Guard" . showChar ' ' . showsPrec 11 cond . showChar ' ' . sp1 11 t . showChar ' ' . sp1 11 f
    where
      sp1 = liftShowsPrec sp sl

instance (Show b, Show a) => Show (UnionBase b a) where
  showsPrec = showsPrec1

instance (Hashable b, Hashable a) => Hashable (UnionBase b a) where
  s `hashWithSalt` (Single a) = s `hashWithSalt` (0 :: Int) `hashWithSalt` a
  s `hashWithSalt` (Guard _ _ c l r) = s `hashWithSalt` (1 :: Int) `hashWithSalt` c `hashWithSalt` l `hashWithSalt` r

-- | Fully reconstruct a 'UnionBase' to maintain the merged invariant.
fullReconstruct :: (SymBoolOp bool) => MergeStrategy bool a -> UnionBase bool a -> UnionBase bool a
fullReconstruct strategy (Guard _ False cond t f) =
  guardWithStrategyInv strategy cond (fullReconstruct strategy t) (fullReconstruct strategy f)
fullReconstruct _ u = u

-- | Use a specific strategy to build a 'Guard' value.
--
-- The merged invariant will be maintained in the result.
guardWithStrategy ::
  (SymBoolOp bool) =>
  MergeStrategy bool a ->
  bool ->
  UnionBase bool a ->
  UnionBase bool a ->
  UnionBase bool a
guardWithStrategy strategy cond t@(Guard _ False _ _ _) f = guardWithStrategy strategy cond (fullReconstruct strategy t) f
guardWithStrategy strategy cond t f@(Guard _ False _ _ _) = guardWithStrategy strategy cond t (fullReconstruct strategy f)
guardWithStrategy strategy cond t f = guardWithStrategyInv strategy cond t f

guardWithStrategyInv ::
  (SymBoolOp bool) =>
  MergeStrategy bool a ->
  bool ->
  UnionBase bool a ->
  UnionBase bool a ->
  UnionBase bool a
guardWithStrategyInv _ (Conc v) t f
  | v = t
  | otherwise = f
guardWithStrategyInv strategy cond (Guard _ True condTrue tt _) f
  | cond == condTrue = guardWithStrategyInv strategy cond tt f
  -- {| nots cond == condTrue || cond == nots condTrue = guardWithStrategyInv strategy cond ft f
guardWithStrategyInv strategy cond t (Guard _ True condFalse _ ff)
  | cond == condFalse = guardWithStrategyInv strategy cond t ff
  -- {| nots cond == condTrue || cond == nots condTrue = guardWithStrategyInv strategy cond t tf -- buggy here condTrue
guardWithStrategyInv (SimpleStrategy m) cond (Single l) (Single r) = Single $ m cond l r
guardWithStrategyInv strategy@(OrderedStrategy idxFun substrategy) cond ifTrue ifFalse = case (ifTrue, ifFalse) of
  (Single _, Single _) -> ssGuard cond ifTrue ifFalse
  (Single _, Guard {}) -> sgGuard cond ifTrue ifFalse
  (Guard {}, Single _) -> gsGuard cond ifTrue ifFalse
  _ -> ggGuard cond ifTrue ifFalse
  where
    ssGuard cond' ifTrue' ifFalse'
      | idxt < idxf = guardWithLeftMost True cond' ifTrue' ifFalse'
      | idxt == idxf = guardWithStrategyInv (substrategy idxt) cond' ifTrue' ifFalse'
      | otherwise = guardWithStrategyInv strategy (nots cond') ifFalse' ifTrue'
      where
        idxt = idxFun $ leftMost ifTrue'
        idxf = idxFun $ leftMost ifFalse'
    {-# INLINE ssGuard #-}
    sgGuard cond' ifTrue' ifFalse'@(Guard _ True condf ft ff)
      | idxft == idxff = ssGuard cond' ifTrue' ifFalse'
      | idxt < idxft = guardWithLeftMost True cond' ifTrue' ifFalse'
      | idxt == idxft = guardWithLeftMost True (cond' ||~ condf) (guardWithStrategyInv (substrategy idxt) cond' ifTrue' ft) ff
      | otherwise = guardWithLeftMost True (nots cond' &&~ condf) ft (guardWithStrategyInv strategy cond' ifTrue' ff)
      where
        idxft = idxFun $ leftMost ft
        idxff = idxFun $ leftMost ff
        idxt = idxFun $ leftMost ifTrue'
    sgGuard _ _ _ = undefined
    {-# INLINE sgGuard #-}
    gsGuard cond' ifTrue'@(Guard _ True condt tt tf) ifFalse'
      | idxtt == idxtf = ssGuard cond' ifTrue' ifFalse'
      | idxtt < idxf = guardWithLeftMost True (cond' &&~ condt) tt $ guardWithStrategyInv strategy cond' tf ifFalse'
      | idxtt == idxf = guardWithLeftMost True (nots cond' ||~ condt) (guardWithStrategyInv (substrategy idxf) cond' tt ifFalse') tf
      | otherwise = guardWithLeftMost True (nots cond') ifFalse' ifTrue'
      where
        idxtt = idxFun $ leftMost tt
        idxtf = idxFun $ leftMost tf
        idxf = idxFun $ leftMost ifFalse'
    gsGuard _ _ _ = undefined
    {-# INLINE gsGuard #-}
    ggGuard cond' ifTrue'@(Guard _ True condt tt tf) ifFalse'@(Guard _ True condf ft ff)
      | idxtt == idxtf = sgGuard cond' ifTrue' ifFalse'
      | idxft == idxff = gsGuard cond' ifTrue' ifFalse'
      | idxtt < idxft = guardWithLeftMost True (cond' &&~ condt) tt $ guardWithStrategyInv strategy cond' tf ifFalse'
      | idxtt == idxft =
        let newCond = ites cond' condt condf
            newIfTrue = guardWithStrategyInv (substrategy idxtt) cond' tt ft
            newIfFalse = guardWithStrategyInv strategy cond' tf ff
         in guardWithLeftMost True newCond newIfTrue newIfFalse
      | otherwise = guardWithLeftMost True (nots cond' &&~ condf) ft $ guardWithStrategyInv strategy cond' ifTrue' ff
      where
        idxtt = idxFun $ leftMost tt
        idxtf = idxFun $ leftMost tf
        idxft = idxFun $ leftMost ft
        idxff = idxFun $ leftMost ff
    ggGuard _ _ _ = undefined
    {-# INLINE ggGuard #-}
guardWithStrategyInv NoStrategy cond ifTrue ifFalse = guardWithLeftMost True cond ifTrue ifFalse
guardWithStrategyInv _ _ _ _ = error "Invariant violated"
{-# INLINE guardWithStrategyInv #-}
