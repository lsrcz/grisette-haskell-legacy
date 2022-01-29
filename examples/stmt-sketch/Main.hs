{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
module Main where
import Parser
import Grisette.Data.SMT.Config
import Interpreter
import Data.SBV (z3)

main :: IO ()
main = do
  r1 <- synthesis (UnboundedReasoning z3) (getSketch "assert ??b" "a")
  print r1
  r2 <- synthesis (UnboundedReasoning z3) (getSketch
     "v1 = ??i;                  \
    \ v2 = ??i;                  \
    \ if (v1 < v2) {             \
    \   v4 = ??v ??{==, <} ??v   \
    \ } else {                   \
    \   v3 = ??v < ??v           \
    \ };                         \
    \ assert v3" "a")
  print r2
  r3 <- synthesis (UnboundedReasoning z3) (getSketch
     "v1 = ??i;                  \
    \ v2 = ??i;                  \
    \ if (v1 < v2) {             \
    \   v4 = ??v ??{==, <} ??v   \
    \ } else {                   \
    \   v3 = v1 < ??v            \
    \ };                         \
    \ assert v3" "a")
  print r3
  {-
  r4 <- synthesis (UnboundedReasoning z3) $ [sketch|a:
    v1 = ??i;
    v2 = ??i;
    if (v1 < v2) {
      v4 = ??v ??{==, <} ??v
    } else {
      v3 = ??v < ??v
    };
    assert v3|]
  print r4
  -}