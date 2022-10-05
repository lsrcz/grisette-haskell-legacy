{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Grisette

testSolver :: GrisetteSMTConfig n -> String -> SymBool -> IO ()
testSolver config solverName formula = do
  m <- solveFormula config formula
  case m of
    Left _ -> putStrLn $ "Grisette solver " ++ solverName ++ " check failed"
    Right mo -> do
      if evaluateToCon mo formula
        then putStrLn $ "Grisette solver " ++ solverName ++ " check successful"
        else putStrLn $ "Grisette solver " ++ solverName ++ " check failed"

main :: IO ()
main = do
  testSolver (UnboundedReasoning z3) "z3" (("a" :: SymInteger) + ("b" :: SymInteger) ==~ 3)
  testSolver (BoundedReasoning @3 boolector) "boolector" (("a" :: SymInteger) + ("b" :: SymInteger) ==~ 3)
