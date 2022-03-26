module Main where

import Test.HSpec.JUnit
import Test.Hspec.Runner
import qualified Spec
import System.Environment

main :: IO ()
main = do
  junitEnabled <- lookupEnv "JUNIT_ENABLED"
  junitOutputDirectory <- lookupEnv "JUNIT_OUTPUT_DIRECTORY"
  case (junitEnabled, junitOutputDirectory) of
    (Just "1", Just path) -> do
      summary@(Summary e f) <- runJUnitSpec Spec.spec (path, "core") defaultConfig
      _ <- putStrLn $ "Total " ++ show e " examples, failed " ++ show f ++ " examples."
      evaluateSummary summary
    _ -> hspec Spec.spec

