{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Grisette
import Interpreter
import Control.Monad.Except

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

data FindRuntimeTypeMismatch = FindRuntimeTypeMismatch

instance ToAssertion FindRuntimeTypeMismatch SymBool (Either Error LitExpr) where
  toAssertion _ (Left (Runtime RuntimeTypeMismatch)) = conc True
  toAssertion _ _ = conc False

main :: IO ()
main = do
  m <- solve FindRuntimeTypeMismatch (UnboundedReasoning z3 {verbose = True}) $ runExceptT $ checkAndInterpretStmtUListU sketch
  case m of
    Right mm -> do
      putStrLn "Not verified, counter example: "
      print $ evaluate False mm sketch
      print $ evaluate True mm sketch
    Left _ -> putStrLn "Verified"
