module Main where

import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
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

main :: IO ()
main = do
  print $ checkAndInterpretStmtList p1
  print $ checkAndInterpretStmtList p2
  print $ checkAndInterpretStmtList p3
