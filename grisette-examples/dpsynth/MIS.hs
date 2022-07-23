{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module MIS where

import Control.Monad
import Core
import Data.List
import Grisette

mis :: (Num a) => ConProgram a
mis =
  ConProgram
    -- pick no_pick
    [0, 0]
    [ ConBinary "+" (ConArg 0) (ConArg 2),
      ConBinary "max" (ConArg 1) (ConArg 2)
    ]
    (ConBinary "max" (ConArg 0) (ConArg 1))
    1

misSketch :: forall a. (SupportedPrim a, Num a) => Program (Sym a)
misSketch =
  genSymSimple
    (CombProgramSpec @a @(Sym a) [0] (CombASTSpec0 1 1 ["zero", "id"] ["+", "max"]) (CombASTSpec0 0 1 [] ["max"]) 2 1)
    "mis"

misSketchOpt :: forall a. (SupportedPrim a, Num a) => Program (Sym a)
misSketchOpt =
  genSymSimple
    (ExtProgramSpec @a @(Sym a) [0] (CombASTSpec0 1 1 ["zero", "id"] ["+", "max"]) "max" 2 1)
    "misopt"

misAlgo :: forall a. (Num a, Ord a) => [a] -> a
misAlgo = go 0 0
  where
    go pick no_pick [] = max pick no_pick
    go pick no_pick (x : xs) = go (no_pick + x) (max pick no_pick) xs

misSpec :: forall a. (SupportedPrim a, Num (Sym a), SOrd SymBool (Sym a)) => [Sym a] -> Sym a
misSpec inputs =
  foldl'
    ( \acc v ->
        let a = if isNotConsecutive v then apply inputs v else 0
         in mrgIte (a >=~ acc :: SymBool) a acc
    )
    0
    allBitStrings
  where
    isNotConsecutive [] = True
    isNotConsecutive [_] = True
    isNotConsecutive (1 : 1 : _) = False
    isNotConsecutive (_ : x : xs) = isNotConsecutive (x : xs)
    allBitStrings = replicateM (length inputs) [0 :: Int, 1]
    apply [] [] = 0
    apply (_ : xs) (0 : ys) = apply xs ys
    apply (x : xs) (1 : ys) = x + apply xs ys
    apply _ _ = undefined
