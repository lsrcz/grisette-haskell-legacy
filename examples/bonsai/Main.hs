module Main where

import STLCMain
import NanoScalaMain

main :: IO ()
main = do
  --putStrLn "SLTC"
  --stlcMain
  putStrLn "DOT"
  dotMain
