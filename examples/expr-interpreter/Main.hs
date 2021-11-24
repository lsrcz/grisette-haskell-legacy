module Main where

import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Interpreter

p1 :: [Stmt]
p1 =
  [ ValueStmt $ mrgSingle $ Ops $ VarExpr $ symb "a"
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
  [ DefineStmt (symb "a") $
      mrgSingle $ Lit $ BoolLit $ symb "b",
    ValueStmt $ mrgSingle $ Ops $ VarExpr $ symb "c"
  ]

main :: IO ()
main = do
  print $ checkAndInterpretStmtList p1
  print $ checkAndInterpretStmtList p2
  print $ checkAndInterpretStmtList p3
