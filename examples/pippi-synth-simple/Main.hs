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
import PippiInterpreter
import Grisette.Data.Class.ToSym
import Text.Printf


-- c1 :: Coord
-- c1 = Coord 10 10

-- e1 :: MovingExpr
-- e1 = CoordExpr c1

-- e2 :: MovingExpr 
-- e2 = MovingExpr (MoveRight $ mrgSingle $ e1)

c1 :: CoordExpr
c1 = CoordLit 10 10

e1 :: MovingExpr
e1 = Coord c1

e2 :: MovingExpr
e2 = Moving (MoveUp $ mrgSingle $ e1)


sketch :: UnionM [UnionM MovingStmt]
sketch = genSym (ListSpec 0 2 (MovingExprSpec 2 1)) "a"

-- main :: IO ()
-- main = do
--   printf "\n=========\n\n"
--   printf "c1: %s\n" (show c1)
--   printf "e1: %s\n" (show e1)
--   printf "e2: %s\n" (show e2)
--   printf "\n=========\n\n"

main :: IO ()
main = do
  m <- solveWith (UnboundedReasoning z3 {verbose = True}) $ case checkAndInterpretStmtUListU sketch of
    ExceptT u -> case mrgFmap
      ( \case
          Left (MovingRuntime MovingRuntimeTypeMismatch) -> conc @SymBool True
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