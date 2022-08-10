{-# LANGUAGE OverloadedStrings #-}

module Main where

import Grisette
import Interpreter

p1 :: [Stmt]
p1 =
  [ ValueStmt $ uOps $ VarExpr "a"
  ]

p2 :: [Stmt]
p2 =
  [ ValueStmt $
      uOps $
        AndExpr (uLit $ BoolLit $ conc True) (uLit $ BoolLit $ conc False)
  ]

p3 :: [Stmt]
p3 =
  [ DefineStmt "a" $ uLit $ BoolLit "b",
    ValueStmt $ uOps $ VarExpr "c"
  ]

sketch :: UnionM [UnionM Stmt]
sketch = genSym (ListSpec 0 2 (ExprSpec 2 1)) "a"

findRuntimeTypeMismatch :: Either Error LitExpr -> SymBool
findRuntimeTypeMismatch (Left (Runtime RuntimeTypeMismatch)) = conc True
findRuntimeTypeMismatch _ = conc False

main :: IO ()
main = do
  m <-
    solveFallable (UnboundedReasoning z3 {verbose = True}) findRuntimeTypeMismatch $
      checkAndInterpretStmtUListU sketch
  case m of
    Right mm -> do
      putStrLn "Not verified, counter example: "
      print $ evaluate False mm sketch
      print $ evaluate True mm sketch
    Left _ -> putStrLn "Verified"
