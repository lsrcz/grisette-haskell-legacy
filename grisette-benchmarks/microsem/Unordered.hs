module Unordered where

import Data.Bifunctor
import Prog
import SymBool

type Unordered a = [(SymBool, a)]

mrgIfUnordered :: (Eq a) => SymBool -> Unordered a -> Unordered a -> Unordered a
mrgIfUnordered cond [] r = fmap (first (ands (nots cond))) r
mrgIfUnordered cond ((c, v) : l) r = case findMergeable r [] of
  (Nothing, collected) -> (ands cond c, v) : mrgIfUnordered cond l collected
  (Just (rc, _), collected) -> (ites cond c rc, v) : mrgIfUnordered cond l collected
  where
    findMergeable [] collected = (Nothing, collected)
    findMergeable (rt@(_, rv) : rl) collected
      | v == rv = (Just rt, rl ++ collected)
      | otherwise = findMergeable rl (rt : collected)

allSymBoolUnordered :: Unordered a -> [SymBool]
allSymBoolUnordered = fmap fst

interpretProgUnordered :: Eq a => Prog a -> Unordered a
interpretProgUnordered (Terminal v) = [(Con True, v)]
interpretProgUnordered (If cond l r) =
  mrgIfUnordered cond (interpretProgUnordered l) (interpretProgUnordered r)

benchmarkUnordered :: Eq a => Prog a -> Int
benchmarkUnordered = length . allSubSymBools . allSymBoolUnordered . interpretProgUnordered
