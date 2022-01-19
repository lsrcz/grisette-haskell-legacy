{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.Except
import Data.SBV
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval (SymEval (symeval))
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.UnionOp
import Grisette.Data.Functor
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.SymPrim
import Interpreter
import Grisette.Data.Class.ToSym

-- ?ident:a
p1 :: [Stmt]
p1 =
  [ ValueStmt $ mrgSingle $ Ops $ VarExpr $ ssymb "a"
  ]

{-
head true
-}

p2 :: [Stmt]
p2 =
  [ ValueStmt $
      mrgSingle $
        Ops $
          AndExpr (mrgSingle $ Lit $ BoolLit $ conc True) (mrgSingle $ Lit $ BoolLit $ conc False)
  ]

{-
  var ?ident:a := ?boolconst:b
  return ?ident:c

  type checking result: throw type error when ?ident:a != ?ident:c

  var v1 := true
  return v2
-}
p3 :: [Stmt]
p3 =
  [ DefineStmt (ssymb "a") $
      mrgSingle $ Lit $ BoolLit $ ssymb "b",
    ValueStmt $ mrgSingle $ Ops $ VarExpr $ ssymb "c"
  ]

{-
   head [true]

   Head (choose [] [a1] [a1, a2])
-}

sketch :: UnionM [UnionM Stmt]
sketch = genSym (ListSpec 0 2 (ExprSpec 2 1)) "a"

main :: IO ()
main = do
  omg
  -- print "omg"
  m <- solveWith (UnboundedReasoning z3 {verbose = True}) $ case checkAndInterpretStmtUListU (toSym p1) of
    ExceptT u -> case mrgFmap
      ( \case
          Left (Typer TypeVarNotFound) -> conc @SymBool True
          _ -> conc False
      )
      u of
      SingleU x -> x
      _ -> error "Bad"
  case m of
    Right mm -> do
      print "Not verified, counter example: "
      -- print $ symeval False mm sketch
      print $ symeval True mm p1
    Left _ -> print "Verified"
