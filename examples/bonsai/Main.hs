module Main where

import LetPolyMain
import NanoScalaMain
import STLCMain
import Utils.Timing

main :: IO ()
main = timeItAll "Overall" $ do
  putStrLn "SLTC"
  stlcMain
  putStrLn "DOT"
  dotMain
  putStrLn "LetPoly"
  letPolyMain
