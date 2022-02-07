{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.Except
import Data.Maybe
import Data.SBV
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval (SymEval (symeval))
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.ToCon
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
e1 = Coord $ mrgSingle c1

e2 :: MovingExpr
e2 = Moving $ mrgSingle $ MoveUp $ mrgSingle $ e1

--
-- | Sketches
--
sketchEmpty :: UnionM [UnionM MovingStmt]
sketchEmpty = genSym (ListSpec 0 2 (MovingExprSpec 2)) "a"

sketchSimple :: UnionM [UnionM MovingStmt]
sketchSimple = toSym
  [ MovingDefineStmt (ssymb "a") $
      mrgSingle $ Coord $ mrgSingle $ CoordLit (ssymb "b") (ssymb "c"),
    MovingValueStmt $ mrgSingle $ MovingVarExpr $ ssymb "a"
  ]

c2 :: MovingExpr 
c2 = (Coord $ mrgSingle $ CoordLit 10 10)

var1 :: SymInteger
var1 = conc 1

c3 :: MovingExpr
c3 = (MovingVarExpr var1)

sketchWithArg :: UnionM [UnionM MovingStmt]
sketchWithArg = toSym
  [ MovingDefineStmt var1 $
      mrgSingle $ c2,
    -- MovingValueStmt $ Moving $ genSym ((MovingExprSpec 2), c2) "b" 
    MovingValueStmt $ mrgSingle $ Moving $ genSym ((MovingExprSpec 5), c3) "b" 
  ]

-- Sirui Argument Trial 
-- genSketchBetter :: ListSpec MovingExprSpec -> String -> CoordExpr -> UnionM [UnionM MovingExpr]
-- genSketchBetter (ListSpec minl maxl movingSpec) = genSymSimple @SymBool (ListSpec minl maxl movingSpec)

-- sketch1 :: CoordExpr -> UnionM [UnionM MovingExpr]
-- sketch1 = genSketchBetter (ListSpec 0 1 (MovingExprSpec 2)) "a"

-- arg :: UnionM CoordExpr
-- arg = genSym @SymBool () "coord" 

-- fullArgSketch :: UnionM [UnionM MovingStmt]
-- fullArgSketch = do
--   l <- arg >>= sketch1 -- l :: [UnionM MovingExpr]
--   mrgReturn $ (mrgSingle . MovingValueStmt) <$> l
  
--
-- | Main
--
main :: IO ()
main = do
  -- printingVars
  verifyTypeChecker
  -- synthesisAttempt
  -- sketchArgumentTrial
  synthesisHoleWithArg


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
      print $ fromJust (toCon $ symeval True mm sketchSimple :: Maybe [ConcMovingStmt])
    Left _ -> print "Couldn't find solution :("
  printEnd

synthesisHoleWithArg :: IO ()
synthesisHoleWithArg = do
  printBeginning "Attempting Synthesis for Program With Hole with Arg"
  m <- solveWith (UnboundedReasoning z3 {verbose = doVerbose}) $ case checkAndInterpretStmtUListU sketchWithArg of
    ExceptT u -> case mrgFmap
      ( \case
          Left _ -> conc @SymBool False
          Right v -> (v ==~ CoordLit 5 10)
      )
      u of
      SingleU x -> x
      _ -> error "Bad"
  case m of
    Right mm -> do
      printf "Found Solution:\n"
      printProgram $ fromJust (toCon $ symeval True mm sketchWithArg :: Maybe [ConcMovingStmt])
    Left _ -> print "Couldn't find solution :("
  printEnd

-- sketchArgumentTrial :: IO ()
-- sketchArgumentTrial = do
--   printBeginning "Attempting Sketch Argument"
--   m <- solveWith (UnboundedReasoning z3 {verbose = doVerbose}) $ case checkAndInterpretStmtUListU fullArgSketch of
--     ExceptT u -> case mrgFmap
--       ( \case
--           Left _ -> conc @SymBool False
--           Right v -> (v ==~ CoordLit 100 100)
--       )
--       u of
--       SingleU x -> x
--       _ -> error "Bad"
--   case m of
--     Right mm -> do
--       printf "Found Solution:\n"
--       print $ fromJust (toCon $ symeval True mm fullArgSketch :: Maybe [ConcMovingStmt])
--     Left _ -> print "Couldn't find solution :("
--   printEnd

--
-- | Printing
--
printBeginning :: String -> IO ()
printBeginning title = printf "\n\n===========\n%s...\n\n" title

printEnd :: IO ()
printEnd = printf "===========\n\n"

printProgram :: [ConcMovingStmt] -> IO ()
printProgram [] = printf "\n"
printProgram (prog:progs) = do
  printf "   %s\n" (show prog)
  printProgram progs