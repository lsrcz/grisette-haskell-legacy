{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Grisette.Data.UnionBase (UnionBase (..), guardWithLeftMost, guardWithStrategy, fullReconstruct) where

import Data.Functor.Classes
import Grisette.Data.Class.Bool
import Grisette.Data.Class.UnionOp
import Grisette.Data.Class.Mergeable
import Data.Hashable
import GHC.Generics
import Grisette.Data.Class.PrimWrapper

data UnionBase b a
  = Single a
  -- left most value / invariant maintained / cond / true branch / false branch
  | Guard a Bool b (UnionBase b a) (UnionBase b a)
  deriving (Generic, Eq)

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
  liftShowsPrec sp sl i (Guard _ _ cond t f) = showParen (i > 10) $
    showString "Guard" . showChar ' ' . showsPrec 11 cond . showChar ' ' . sp1 11 t . showChar ' ' . sp1 11 f
    where sp1 = liftShowsPrec sp sl

instance (Show b, Show a) => Show (UnionBase b a) where
  showsPrec = showsPrec1

instance (Hashable b, Hashable a) => Hashable (UnionBase b a) where
  s `hashWithSalt` (Single a) = s `hashWithSalt` (0 :: Int) `hashWithSalt` a
  s `hashWithSalt` (Guard _ _ c l r) = s `hashWithSalt` (1 :: Int) `hashWithSalt` c `hashWithSalt` l `hashWithSalt` r

fullReconstruct :: (SymBoolOp bool) => MergeStrategy bool a -> UnionBase bool a -> UnionBase bool a
fullReconstruct strategy (Guard _ False cond t f) =
  guardWithStrategy strategy cond (fullReconstruct strategy t) (fullReconstruct strategy f)
fullReconstruct _ u = u

guardWithStrategy :: (SymBoolOp bool) => MergeStrategy bool a ->
   bool -> UnionBase bool a -> UnionBase bool a -> UnionBase bool a
guardWithStrategy strategy cond t@(Guard _ False _ _ _) f = guardWithStrategy strategy cond (fullReconstruct strategy t) f
guardWithStrategy strategy cond t f@(Guard _ False _ _ _) = guardWithStrategy strategy cond t (fullReconstruct strategy f)
guardWithStrategy _ (Conc True) t _ = t
guardWithStrategy _ (Conc False) _ f = f
guardWithStrategy strategy cond (Guard _ True condTrue tt _) f
  | cond == condTrue = guardWithStrategy strategy cond tt f
guardWithStrategy strategy cond (Guard _ True condTrue _ ft) f
  | nots cond == condTrue || cond == nots condTrue = guardWithStrategy strategy cond ft f
guardWithStrategy strategy cond t (Guard _ True condFalse _ ff)
  | cond == condFalse = guardWithStrategy strategy cond t ff
guardWithStrategy strategy cond t (Guard _ True condTrue tf _)
  | nots cond == condTrue || cond == nots condTrue = guardWithStrategy strategy cond t tf
guardWithStrategy (SimpleStrategy m) cond (SingleU l) (SingleU r) = SingleU $ m cond l r
guardWithStrategy strategy@(OrderedStrategy idxFun substrategy) cond ifTrue ifFalse = case (ifTrue, ifFalse) of
  (SingleU _, SingleU _) -> ssGuard cond ifTrue ifFalse
  (SingleU _, GuardU {}) -> sgGuard cond ifTrue ifFalse
  (GuardU {}, SingleU _) -> gsGuard cond ifTrue ifFalse
  (GuardU {}, GuardU {}) -> ggGuard cond ifTrue ifFalse
  _ -> undefined
  where
    ssGuard cond' ifTrue' ifFalse'
      | idxt < idxf = guardWithLeftMost True cond' ifTrue' ifFalse'
      | idxt == idxf = guardWithStrategy (substrategy idxt) cond' ifTrue' ifFalse'
      | otherwise = guardWithStrategy strategy (nots cond') ifFalse' ifTrue'
      where
        idxt = idxFun $ leftMost ifTrue'
        idxf = idxFun $ leftMost ifFalse'
    sgGuard cond' ifTrue' ifFalse'@(Guard _ True condf ft ff)
      | idxft == idxff = ssGuard cond' ifTrue' ifFalse'
      | idxt < idxft = guardWithLeftMost True cond' ifTrue' ifFalse'
      | idxt == idxft = guardWithLeftMost True (cond' ||~ condf) (guardWithStrategy (substrategy idxt) cond' ifTrue' ft) ff
      | otherwise = guardWithLeftMost True (nots cond' &&~ condf) ft (guardWithStrategy strategy cond' ifTrue' ff)
      where
        idxft = idxFun $ leftMost ft
        idxff = idxFun $ leftMost ff
        idxt = idxFun $ leftMost ifTrue'
    sgGuard _ _ _ = undefined
    gsGuard cond' ifTrue'@(Guard _ True condt tt tf) ifFalse'
      | idxtt == idxtf = ssGuard cond' ifTrue' ifFalse'
      | idxtt < idxf = guardWithLeftMost True (cond' &&~ condt) tt $ guardWithStrategy strategy cond' tf ifFalse'
      | idxtt == idxf = guardWithLeftMost True (nots cond' ||~ condt) (guardWithStrategy (substrategy idxf) cond' tt ifFalse') tf
      | otherwise = guardWithLeftMost True (nots cond') ifFalse' ifTrue'
      where
        idxtt = idxFun $ leftMost tt
        idxtf = idxFun $ leftMost tf
        idxf = idxFun $ leftMost ifFalse'
    gsGuard _ _ _ = undefined
    ggGuard cond' ifTrue'@(Guard _ True condt tt tf) ifFalse'@(Guard _ True condf ft ff)
      | idxtt == idxtf = sgGuard cond' ifTrue' ifFalse'
      | idxft == idxff = gsGuard cond' ifTrue' ifFalse'
      | idxtt < idxft = guardWithLeftMost True (cond' &&~ condt) tt $ guardWithStrategy strategy cond' tf ifFalse'
      | idxtt == idxft =
        let newCond = ites cond' condt condf
            newIfTrue = guardWithStrategy (substrategy idxtt) cond' tt ft
            newIfFalse = guardWithStrategy strategy cond' tf ff
         in guardWithLeftMost True newCond newIfTrue newIfFalse
      | otherwise = guardWithLeftMost True (nots cond' &&~ condf) ft $ guardWithStrategy strategy cond' ifTrue' ff
      where
        idxtt = idxFun $ leftMost tt
        idxtf = idxFun $ leftMost tf
        idxft = idxFun $ leftMost ft
        idxff = idxFun $ leftMost ff
    ggGuard _ _ _ = undefined
guardWithStrategy NoStrategy cond ifTrue ifFalse = guardWithLeftMost True cond ifTrue ifFalse
guardWithStrategy _ _ _ _ = error "Invariant violated"
