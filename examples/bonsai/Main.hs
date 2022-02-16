module Main where

-- import STLCMain
import NanoScalaMain
-- import LetPolyMain
import Utils.Timing

main :: IO ()
main = timeItAll "Overall" $ do
  -- putStrLn "SLTC"
  -- stlcMain
  putStrLn "DOT"
  dotMain
  -- putStrLn "LetPoly"
  -- letPolyMain
