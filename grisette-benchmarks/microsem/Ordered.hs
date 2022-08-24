module Ordered where

import Prog
import SymBool

data Ordered a = Single a | ITE SymBool a (Ordered a) deriving (Show)

reorder :: Eq a => a -> Ordered a -> Ordered a
reorder v = go
  where
    go (Single x) = Single x
    go r@(ITE c l1 r1)
      | v == l1 = r
      | otherwise = case go r1 of
          Single a | a == v -> ITE (nots c) a (Single l1)
          ITE sb a or' | a == v -> ITE (ands (nots c) sb) a (ITE c l1 or')
          gr -> ITE c l1 gr
{-# INLINE reorder #-}

mrgIfOrderedNaive :: (Eq a) => SymBool -> Ordered a -> Ordered a -> Ordered a
mrgIfOrderedNaive cond l@(Single a) r = case reorder a r of
  Single b | a == b -> l
  ITE c1 b rr | a == b -> ITE (ors cond c1) a rr
  _ -> ITE cond a r
mrgIfOrderedNaive cond (ITE c a ll) r = case reorder a r of
  Single b | a == b -> ITE (ites cond c (Con True)) a ll
  ITE c1 b rr | a == b -> ITE (ites cond c c1) a $ mrgIfOrderedNaive cond ll rr
  _ -> ITE (ands cond c) a $ mrgIfOrderedNaive cond ll r
{-# INLINE mrgIfOrderedNaive #-}

allSymBoolOrdered :: Ordered a -> [SymBool]
allSymBoolOrdered (ITE c _ r) = c : allSymBoolOrdered r
allSymBoolOrdered _ = []

interpretProgOrderedNaive :: Eq a => Prog a -> Ordered a
interpretProgOrderedNaive (Terminal v) = Single v
interpretProgOrderedNaive (If c l r) = mrgIfOrderedNaive c (interpretProgOrderedNaive l) (interpretProgOrderedNaive r)
{-# INLINE interpretProgOrderedNaive #-}

mrgIfOrderedSorted :: (Ord a) => SymBool -> Ordered a -> Ordered a -> Ordered a
mrgIfOrderedSorted cond (Single a) (Single b)
  | a < b = ITE cond a (Single b)
  | a == b = Single a
  | otherwise = ITE (nots cond) b (Single a)
mrgIfOrderedSorted cond (Single a) b@(ITE bc bl br)
  | a < bl = ITE cond a b
  | a == bl = ITE (ors cond bc) bl br
  | otherwise = ITE (ands (nots cond) bc) bl $ mrgIfOrderedSorted cond (Single a) br
mrgIfOrderedSorted cond a@(ITE ac al ar) (Single b)
  | al < b = ITE (ands cond ac) al $ mrgIfOrderedSorted cond ar (Single b)
  | al == b = ITE (ors (nots cond) ac) al ar
  | otherwise = ITE (nots cond) b a
mrgIfOrderedSorted cond a@(ITE ac al ar) b@(ITE bc bl br)
  | al < bl = ITE (ands cond ac) al $ mrgIfOrderedSorted cond ar b
  | al == bl = ITE (ites cond ac bc) al $ mrgIfOrderedSorted cond ar br
  | otherwise = ITE (ands (nots cond) bc) bl $ mrgIfOrderedSorted cond a br
{-# INLINE mrgIfOrderedSorted #-}

interpretProgOrderedSorted :: Ord a => Prog a -> Ordered a
interpretProgOrderedSorted (Terminal v) = Single v
interpretProgOrderedSorted (If c l r) = mrgIfOrderedSorted c (interpretProgOrderedSorted l) (interpretProgOrderedSorted r)
{-# INLINE interpretProgOrderedSorted #-}

benchmarkNaive :: Eq a => Prog a -> Int
benchmarkNaive = length . allSubSymBools . allSymBoolOrdered . interpretProgOrderedNaive

benchmarkSorted :: Ord a => Prog a -> Int
benchmarkSorted = length . allSubSymBools . allSymBoolOrdered . interpretProgOrderedSorted
