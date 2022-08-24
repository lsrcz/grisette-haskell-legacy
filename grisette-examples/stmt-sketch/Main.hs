{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Grisette
import Interpreter
import Parser

main :: IO ()
main = do
  r1 <- synthesis (UnboundedReasoning z3) doSynthesisTranslation (getSketch "assert ??b" "a")
  print r1
  r2 <-
    synthesis
      (UnboundedReasoning z3)
      doSynthesisTranslation
      ( getSketch
          "v1 = ??i;                   \
          \ v2 = ??i;                  \
          \ v3 = ??b;                  \
          \ if (v1 < v2) {             \
          \   v5 = ??v ??{==, <} ??v   \
          \ } else {                   \
          \   v4 = ??v < ??v           \
          \ };                         \
          \ assert v4"
          "a"
      )
  print r2
  r3 <-
    synthesis
      (UnboundedReasoning z3)
      doSynthesisTranslation
      ( getSketch
          "v1 = ??i;                   \
          \ v2 = ??i;                  \
          \ v3 = ??b;                  \
          \ if (v1 < v2) {             \
          \   v5 = ??v ??{==, <} ??v   \
          \ } else {                   \
          \   v4 = ??v < ??v           \
          \ };                         \
          \ assert v4"
          "a"
      )
  print r3
  r4 <-
    synthesis
      (UnboundedReasoning z3)
      getTypeErrorTranslation
      ( getSketch
          "v1 = ??i;                   \
          \ v2 = ??i;                  \
          \ v3 = ??b;                  \
          \ if (v1 < v2) {             \
          \   v5 = ??v ??{==, <} ??v   \
          \ } else {                   \
          \   v4 = ??v < ??v           \
          \ };                         \
          \ assert v4"
          "a"
      )
  print r4

{-
  rquasiquoter <- synthesis DoSynthesis (UnboundedReasoning z3) $ [sketch|a:
    v1 = ??i;
    v2 = ??i;
    if (v1 < v2) {
      v4 = ??v ??{==, <} ??v
    } else {
      v3 = ??v < ??v
    };
    assert v3|]
  print rquasiquoter
-}
