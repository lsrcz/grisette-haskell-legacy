{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Benchmark.Queries
import Control.DeepSeq
import Denotation
import Equal
import Grisette.Backend.SBV
import Grisette.Core
import Utils.Timing

main :: IO ()
main = timeItAll "Overall" $ do
  let r1 = $$(denoteSql q4)
  let r1r = $$(denoteSql q4r)
  let cond = $$(verifCondition q4 q4r)
  _ <- timeItAll "all" $ cond `deepseq` return ()
  r <- timeItAll "solve" $ solveWith (UnboundedReasoning z3 {verbose = False, timing = PrintTiming}) cond
  case r of
    Left _ -> putStrLn "Verified"
    Right m -> do
      putStrLn "Found counter example:"
      putStrLn "t:"
      print $ symeval True m t
      putStrLn "tr:"
      print $ symeval True m tr
      putStrLn "ta:"
      print $ symeval True m ta
      putStrLn "tb:"
      print $ symeval True m tb
      putStrLn "q4 execution result:"
      print $ symeval True m r1
      putStrLn "q4r execution result:"
      print $ symeval True m r1r
