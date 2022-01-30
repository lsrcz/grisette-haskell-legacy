{-# LANGUAGE OverloadedStrings #-}

module Main where

import Expr
import Grisette.Backend.SBV
import Parser

main :: IO ()
main = do
  s <- synthesis (UnboundedReasoning z3) (getSketch "1 + (??[5,4] ??{*, +} 2)" "a") 7
  print s
