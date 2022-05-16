{-# LANGUAGE OverloadedStrings #-}

module MMM where

import Core

mmm :: ConProgram Integer
mmm =
  ConProgram
    -- ign pos neg
    [0, 0, 0]
    [ ConBinary "max" (ConArg 2) (ConArg 3),
      ConBinary
        "max"
        (ConBinary "+" (ConArg 1) (ConArg 0))
        (ConBinary "+" (ConArg 3) (ConArg 0)),
      ConBinary
        "max"
        (ConBinary "-" (ConArg 1) (ConArg 0))
        (ConBinary "-" (ConArg 2) (ConArg 0))
    ]
    (ConBinary "max" (ConBinary "max" (ConArg 0) (ConArg 1)) (ConArg 2))
    1

mmmAlgo :: [Integer] -> Integer
mmmAlgo = go 0 0 0
  where
    go ign pos neg [] = max (max ign pos) neg
    go ign pos neg (x : xs) = go (max pos neg) (max (ign + x) (neg + x)) (max (ign - x) (pos - x)) xs
