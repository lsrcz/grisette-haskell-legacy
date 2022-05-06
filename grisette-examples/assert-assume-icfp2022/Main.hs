{-# LANGUAGE OverloadedStrings #-}
module Main where

import Grisette
import Control.Monad.Except


-- In Rosette, the assume is used to restrict the valid input space, and the assert is used to specify the correctness conditions
-- The following SolverTranslation instances simulates Rosette's verify.
data RosetteInterpretation = RosetteInterpretation

instance SolverErrorTranslation RosetteInterpretation VerificationConditions where
  -- Translating AssertionViolation to True means that we are trying to find a counterexample that
  -- terminates with an assertion violation
  errorTranslation _ AssertionViolation = True
  -- Translating AssumptionViolation to False means that we are trying to find a counterexample that
  -- should not terminate with an assumption violation
  errorTranslation _ AssumptionViolation = False

instance SolverTranslation RosetteInterpretation SymBool VerificationConditions a where
  -- The counterexample should not terminate normally.
  valueTranslation _ _ = conc False

-- For example, if we are going to verify the following program by trying to find a counterexample, we will get nothing.
-- 'assume (x >~ 5)' performs a symbolic comparison, and restricts that a valid value for 'x' should be greater than 5.
-- Under this assumption, we cannot find a counterexample such that 'x' is less than or equal to 4.
a1 :: SymInteger -> ExceptT VerificationConditions UnionM ()
a1 x = do
  symAssume (x >~ 5)
  symAssert (x >~ 4)

-- If we are going to verify the following program by trying to find a counter example, we will get a counterexample where x is 6.
-- That input meets the assumption that x is greater than 5, but violates the assertion that x is greater than 6.
a2 :: SymInteger -> ExceptT VerificationConditions UnionM ()
a2 x = do
  symAssume (x >~ 5)
  symAssert (x >~ 6)

main :: IO ()
main = do
  res1 <- solveWithExcept RosetteInterpretation (UnboundedReasoning z3) (a1 "x")
  print res1
  -- Left Unsat
  res2 <- solveWithExcept RosetteInterpretation (UnboundedReasoning z3) (a2 "x")
  print res2
  -- Right (Model (fromList [(x :: Integer,6 :: Integer)]))
