module Main where

import System.FilePath.Glob (glob)
import Test.DocTest (doctest)

main :: IO ()
main = do
  fp1 <- glob "../grisette-core/src/**/*.hs"
  fp2 <- glob "../grisette-symir/src/**/*.hs"
  doctest $ ["-i../grisette-core/src/", "-i../grisette-symir/src/"] ++ fp1 ++ fp2