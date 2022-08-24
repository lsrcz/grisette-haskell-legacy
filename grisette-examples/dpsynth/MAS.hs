{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module MAS where

import Control.Monad
import Core
import Data.Foldable
import Grisette

mas :: Num a => ConProgram a
mas =
  ConProgram
    -- suffix_pos suffix_neg best
    [0, 0, 0]
    [ ConBinary "+" (ConBinary "max" (ConUnary "zero" (ConArg 0)) (ConArg 2)) (ConArg 0),
      ConBinary "-" (ConBinary "max" (ConUnary "zero" (ConArg 0)) (ConArg 1)) (ConArg 0),
      ConBinary "max" (ConBinary "max" (ConArg 1) (ConArg 2)) (ConArg 3)
    ]
    (ConBinary "max" (ConBinary "max" (ConArg 0) (ConArg 1)) (ConArg 2))
    1

masSynthed1 :: Num a => ConProgram a
masSynthed1 =
  ConProgram
    [0, 0]
    [ ConBinary "max" (ConBinary "max" (ConBinary "+" (ConArg 2) (ConUnary "-" (ConArg 0))) (ConArg 2)) (ConArg 1),
      ConBinary "max" (ConBinary "+" (ConBinary "+" (ConUnary "-" (ConArg 2)) (ConArg 1)) (ConArg 0)) (ConBinary "max" (ConArg 0) (ConUnary "zero" (ConArg 0)))
    ]
    (ConBinary "max" (ConArg 0) (ConArg 1))
    1

masSynthedOpt1 :: Num a => ConProgram a
masSynthedOpt1 =
  ConProgram
    [0, 0, 0]
    [ ConBinary "max" (ConBinary "+" (ConArg 3) (ConArg 0)) (ConBinary "+" (ConArg 0) (ConUnary "-" (ConArg 1))),
      ConBinary
        "max"
        (ConBinary "max" (ConArg 1) (ConArg 3))
        (ConBinary "max" (ConArg 2) (ConArg 0)),
      ConBinary
        "max"
        ( ConBinary
            "max"
            (ConBinary "max" (ConUnary "-" (ConArg 0)) (ConUnary "zero" (ConArg 2)))
            (ConBinary "+" (ConUnary "-" (ConArg 0)) (ConArg 1))
        )
        (ConUnary "-" $ ConArg 3)
    ]
    (ConBinary "max" (ConBinary "max" (ConArg 0) (ConArg 1)) (ConArg 2))
    1

masSynthedOptAlgo1 :: (Num a, Ord a, Show a) => [a] -> a
masSynthedOptAlgo1 = go 0 0 0
  where
    go p1 p2 p3 [] = max p1 $ max p2 p3
    go p1 p2 p3 (a : as) =
      go
        (max (p3 + a) (a - p1))
        (max p1 (max p3 (max p2 a)))
        (max (max (-a) 0) (max (p1 - a) (-p3)))
        as

masAlgo :: (Num a, Ord a) => [a] -> a
masAlgo = go 0 0 0
  where
    go suffix_pos suffix_neg best [] = max (max suffix_pos suffix_neg) best
    go suffix_pos suffix_neg best (x : xs) =
      go (max 0 suffix_neg + x) (max 0 suffix_pos - x) (max (max suffix_pos suffix_neg) best) xs

masSketch :: forall a. (SupportedPrim a, Num a) => Program (Sym a)
masSketch =
  genSymSimple
    (CombProgramSpec @a @(Sym a) [0] (CombASTSpec0 1 3 ["zero", "id", "-"] ["+", "max"]) (CombASTSpec0 0 2 [] ["max"]) 3 1)
    "mas"

masSketchOpt :: forall a. (SupportedPrim a, Num a) => Program (Sym a)
masSketchOpt =
  genSymSimple
    (ExtProgramSpec @a @(Sym a) [0] (CombASTSpec0 1 1 ["zero", "id", "-"] ["+", "max"]) "max" 3 1)
    "mas"

masSketch1 :: forall a. (SupportedPrim a, Num a) => Program (Sym a)
masSketch1 =
  genSymSimple
    (CombProgramSpec @a @(Sym a) [0] (CombASTSpec0 1 3 ["zero", "id", "-"] ["+", "max"]) (CombASTSpec0 0 2 [] ["max"]) 2 1)
    "mas"

masSpec :: forall a. (SupportedPrim a, Num (Sym a), SOrd SymBool (Sym a)) => [Sym a] -> Sym a
masSpec inputs =
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
    isConsecutive0 (-1 : xs) = isConsecutivem1 xs
    isConsecutive0 (_ : _) = undefined
    isConsecutive1 [] = True
    isConsecutive1 (1 : _) = False
    isConsecutive1 (-1 : xs) = isConsecutivem1 xs
    isConsecutive1 (0 : xs) = all (== 0) xs
    isConsecutive1 (_ : _) = undefined
    isConsecutivem1 [] = True
    isConsecutivem1 (-1 : _) = False
    isConsecutivem1 (1 : xs) = isConsecutive1 xs
    isConsecutivem1 (0 : xs) = all (== 0) xs
    isConsecutivem1 (_ : _) = undefined
    allBitStrings = replicateM (length inputs) [0 :: Int, 1, -1]
    apply [] [] = 0
    apply (_ : xs) (0 : ys) = apply xs ys
    apply (x : xs) (1 : ys) = x + apply xs ys
    apply (x : xs) (-1 : ys) = apply xs ys - x
    apply _ _ = undefined
