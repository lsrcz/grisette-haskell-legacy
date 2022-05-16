{-# LANGUAGE OverloadedStrings #-}

module ASSEM where
import Core

assem :: ConProgram Integer
assem =
  ConProgram
    -- line1 line2
    [0, 0]
    [ ConBinary
        "min"
        (ConBinary "+" (ConArg 2) (ConArg 0))
        (ConBinary "+" (ConArg 3) (ConArg 1)),
      ConBinary
        "min"
        (ConBinary "+" (ConArg 3) (ConArg 0))
        (ConBinary "+" (ConArg 2) (ConArg 1))
    ]
    (ConBinary "min" (ConArg 0) (ConArg 1))
    -- stay switch
    2

assemAlgo :: [(Integer, Integer)] -> Integer
assemAlgo = go 0 0
  where
    go line1 line2 [] = min line1 line2
    go line1 line2 ((stay, switch) : xs) =
      go (min (line1 + stay) (line2 + switch)) (min (line2 + stay) (line1 + switch)) xs