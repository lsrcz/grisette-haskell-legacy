{-# LANGUAGE OverloadedStrings #-}

module Main where

import Expr
import Grisette
import Parser

main :: IO ()
main = do
  s <- synthesis (UnboundedReasoning z3) (getSketch "1 + (??[5,4] ??{*, +} 2)" "a") 7
  print s
