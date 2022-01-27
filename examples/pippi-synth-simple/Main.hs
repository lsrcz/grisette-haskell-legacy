{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.Except
import Data.SBV
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval (SymEval (symeval))
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.UnionOp
import Grisette.Data.Functor
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.SymPrim
-- import PippiInterpreter
import PippiInterpreter2
import Grisette.Data.Class.ToSym
import Text.Printf

--
-- | Example Expressions
--
c1 :: CoordExpr
c1 = CoordLit (ssymb "a") (ssymb "b")

e1 :: MovingExpr
e1 = Coord c1

e2 :: MovingExpr
e2 = Moving (MoveUp $ mrgSingle $ e1)

--
-- | Sketches
--
sketchEmpty :: UnionM [UnionM MovingStmt]
sketchEmpty = genSym (ListSpec 0 2 (MovingExprSpec 2)) "a"

{-
  var ?ident:a := CoordLit ?ident:b ?ident:c
  return ?ident:a
-}
sketchSimple :: UnionM [UnionM MovingStmt]
sketchSimple = toSym
  [ MovingDefineStmt (ssymb "a") $
      mrgSingle $ Coord $ CoordLit (ssymb "b") (ssymb "c"),
    MovingValueStmt $ mrgSingle $ MovingVarExpr $ ssymb "a"
  ]

{-
  var ?ident:a := CoordLit 10 10
  var ?ident:b := ?:Moving:x -- TODO how do i pass in an argument to this function?
  return ?ident:a
-}
-- sketchMoveUp :: [MovingStmt]
-- sketchMoveUp = toSym
--   [ MovingDefineStmt (ssymb "a") $
--       mrgSingle $ Coord $ CoordLit (ssymb "b") (ssymb "c"),
--     MovingValueStmt $ mrgSingle $ Moving $ MovingVarExpr $ ssymb "a"
--   ]

c2 :: CoordExpr 
c2 = CoordLit 10 10

sketchWithArg :: UnionM [UnionM MovingStmt]
sketchWithArg = toSym
  [ MovingDefineStmt (conc 1) $
      mrgSingle $ Coord $ c2,
    MovingValueStmt $ Moving <$> genSym ((MovingExprSpec 2), c2) "b" 
  ]



-- Sirui Argument Trial 
-- genSketch :: ListSpec Int -> String -> Coord -> UnionM [UnionM Move]
-- genSketch (ListSpec minl maxl sub) name coord = genSym (ListSpec minl maxl (sub, coord)) name

genSketchBetter :: ListSpec MovingExprSpec -> String -> CoordExpr -> UnionM [UnionM MovingExpr]
genSketchBetter (ListSpec minl maxl movingSpec) = genSymSimple @SymBool (ListSpec minl maxl movingSpec)

-- sketch :: Coord -> UnionM [UnionM Move]
-- sketch = genSketch (ListSpec 0 1 (MovingExprSpec 1)) "a"

sketch1 :: CoordExpr -> UnionM [UnionM MovingExpr]
sketch1 = genSketchBetter (ListSpec 0 1 (MovingExprSpec 2)) "a"

-- let arg = genSym @SymBool () "coord" :: UnionM CoordExpr

-- fullArgSketch :: UnionM [UnionM MovingStmt]
-- fullArgSketch = toSym
--   [ MovingValueStmt $ (sketch1 <$> genSym @SymBool () "coord")
--   ]

--
-- | Main
--
main :: IO ()
main = do
  -- printingVars
  -- verifyTypeChecker
  -- synthesisAttempt
  -- print sketchWithArg
  sketchArgumentTrial






--
-- | Tasks
--
doVerbose :: Bool
doVerbose = False

printingVars :: IO ()
printingVars = do
  printBeginning "Printing Variables"
  printf "c1: %s\n" (show c1)
  printf "e1: %s\n" (show e1)
  printf "e2: %s\n" (show e2)
  printf "sketchSimple: %s\n" (show sketchSimple)
  printEnd

verifyTypeChecker :: IO ()
verifyTypeChecker = do
  printBeginning "Verifying Type Checker"
  m <- solveWith (UnboundedReasoning z3 {verbose = doVerbose}) $ case checkAndInterpretStmtUListU sketchEmpty of
    ExceptT u -> case mrgFmap
      ( \case
          Left (MovingRuntime MovingRuntimeTypeMismatch) -> conc @SymBool True
          _ -> conc @SymBool False
      )
      u of
      SingleU x -> x
      _ -> error "Bad"
  case m of
    Right mm -> do
      printf "Not verified, counter example:\n"
      print $ symeval False mm sketchEmpty
      print $ symeval True mm sketchEmpty
    Left _ -> print "Verified"
  printEnd

synthesisAttempt :: IO ()
synthesisAttempt = do
  printBeginning "Attempting Synthesis"
  m <- solveWith (UnboundedReasoning z3 {verbose = doVerbose}) $ case checkAndInterpretStmtUListU sketchSimple of
    ExceptT u -> case mrgFmap
      ( \case
          Left _ -> conc @SymBool False
          Right v -> (v ==~ CoordLit 1 1)
      )
      u of
      SingleU x -> x
      _ -> error "Bad"
  case m of
    Right mm -> do
      printf "Found Solution:\n"
      print $ symeval True mm sketchSimple
    Left _ -> print "Couldn't find solution :("
  printEnd


sketchArgumentTrial :: IO ()
sketchArgumentTrial = do
  printBeginning "Attempting Sketch Argument"

  let arg :: UnionM CoordExpr
      arg = genSym @SymBool () "coord" 
      
  let concSketch :: UnionM [UnionM MovingExpr]
      concSketch = sketch1 (CoordLit (conc 0) (conc 0)) 

  let argSketch :: UnionM [UnionM MovingExpr]
      argSketch = arg >>= sketch1 

  let argTypeTo_checkAndInterpretStmtUListU :: UnionM [UnionM MovingStmt]
      argTypeTo_checkAndInterpretStmtUListU = undefined


  -- printf "arg: %s\n\n" (show arg)
  -- printf "argSketch: %s\n\n" (show argSketch)

  -- let coord = getSingle arg
  -- printf "coord: %s\n\n" (show <$> arg)

  -- m <- solveWith (UnboundedReasoning z3 {verbose = doVerbose}) $ case checkAndInterpretStmtUListU (toSym argSketch) of
  --   ExceptT u -> case mrgFmap
  --     ( \case
  --         Left _ -> conc @SymBool False
  --         Right v -> (v ==~ CoordLit 1 1)
  --     )
  --     u of
  --     SingleU x -> x
  --     _ -> error "Bad"
  -- case m of
  --   Right mm -> do
  --     printf "Found Solution:\n"
  --     print $ symeval True mm sketchSimple
  --   Left _ -> print "Couldn't find solution :("
  printEnd

--
-- | Printing
--
printBeginning :: String -> IO ()
printBeginning title = printf "\n\n===========\n%s...\n\n" title

printEnd :: IO ()
printEnd = printf "===========\n\n"
