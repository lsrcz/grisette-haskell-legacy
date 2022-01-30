{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.Except
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Interpreter

p1 :: [Stmt]
p1 =
  [ ValueStmt $ mrgSingle $ Ops $ VarExpr $ ssymb "a"
  ]

p2 :: [Stmt]
p2 =
  [ ValueStmt $
      mrgSingle $
        Ops $
          AndExpr (mrgSingle $ Lit $ BoolLit $ conc True) (mrgSingle $ Lit $ BoolLit $ conc False)
  ]

p3 :: [Stmt]
p3 =
  [ DefineStmt (ssymb "a") $
      mrgSingle $ Lit $ BoolLit $ ssymb "b",
    ValueStmt $ mrgSingle $ Ops $ VarExpr $ ssymb "c"
  ]

sketch :: UnionM [UnionM Stmt]
sketch = genSym (ListSpec 0 2 (ExprSpec 2 1)) "a"

main :: IO ()
main = do
  m <- solveWith (UnboundedReasoning z3 {verbose = True}) $ case checkAndInterpretStmtUListU sketch of
    ExceptT u -> case mrgFmap
      ( \case
          Left (Runtime RuntimeTypeMismatch) -> conc @SymBool True
          _ -> conc False
      )
      u of
      SingleU x -> x
      _ -> error "Bad"
  case m of
    Right mm -> do
      print "Not verified, counter example: "
      print $ symeval False mm sketch
      print $ symeval True mm sketch
    Left _ -> print "Verified"
