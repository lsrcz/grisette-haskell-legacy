module Main where

import Grisette.TestUtils.Runner
import qualified Spec

main :: IO ()
main = runGrisetteTests "vector-sized" Spec.spec
