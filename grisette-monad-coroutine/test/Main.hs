module Main where

import Grisette.TestUtils.Runner
import qualified Spec

main :: IO ()
main = runGrisetteTests "monad-coroutine" Spec.spec
