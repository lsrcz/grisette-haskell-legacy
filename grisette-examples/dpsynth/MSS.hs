{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module MSS where

import Control.Monad
import Core
import Data.List
import Data.Proxy
import Grisette

mss :: Num a => ConProgram a
mss =
  ConProgram
    -- suffix best
    [0, 0]
    [ ConBinary "+" (ConBinary "max" (ConUnary "zero" (ConArg 0)) (ConUnary "id" (ConArg 1))) (ConUnary "id" (ConArg 0)),
      ConBinary "max" (ConUnary "id" (ConArg 1)) (ConUnary "id" (ConArg 2))
    ]
    (ConBinary "max" (ConUnary "id" (ConArg 0)) (ConUnary "id" (ConArg 1)))
    1

mssSketch :: forall a. (SupportedPrim a, Num a) => Program (Sym a)
mssSketch =
  genSymSimple (Proxy :: Proxy SymBool)
    (CombProgramSpec @a @(Sym a) [0] (CombASTSpec0 1 2 ["zero", "id"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 2 1)
    "mss"

mssAlgo :: (Num a, Ord a) => [a] -> a
mssAlgo = go 0 0
  where
    go suffix best [] = max suffix best
    go suffix best (x : xs) = go (max 0 suffix + x) (max suffix best) xs

mssAlgo2 :: (Num a, Ord a) => [a] -> a
mssAlgo2 = go 0 0
  where
    go suffix best [] = max suffix best
    go suffix best (x : xs) = go (max 0 suffix + x) (max (max suffix x) best) xs

mssAlgo1 :: (Num a, Ord a) => [a] -> a
mssAlgo1 = go 0 0
  where
    go max_so_far _ [] = max_so_far
    go max_so_far max_ending_here (x : xs) =
      let new_max_ending_here = max_ending_here + x
       in go (max max_so_far new_max_ending_here) (max 0 new_max_ending_here) xs

mssSpec :: forall a. (SupportedPrim a, Num (Sym a), SOrd SymBool (Sym a)) => [Sym a] -> Sym a
mssSpec inputs =
  foldl'
    ( \acc v ->
        let a = if isConsecutive0 v then apply inputs v else 0
         in mrgIte (a >=~ acc :: SymBool) a acc
    )
    0
    allBitStrings
  where
    isConsecutive0 [] = True
    isConsecutive0 (0 : xs) = isConsecutive0 xs
    isConsecutive0 (1 : xs) = isConsecutive1 xs
    isConsecutive0 (_ : _) = undefined
    isConsecutive1 [] = True
    isConsecutive1 (1 : xs) = isConsecutive1 xs
    isConsecutive1 (0 : xs) = all (== 0) xs
    isConsecutive1 (_ : _) = undefined
    allBitStrings = replicateM (length inputs) [0 :: Int, 1]
    apply [] [] = 0
    apply (_ : xs) (0 : ys) = apply xs ys
    apply (x : xs) (1 : ys) = x + apply xs ys
    apply _ _ = undefined
