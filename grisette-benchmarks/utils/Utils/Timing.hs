{-# LANGUAGE OverloadedStrings #-}

module Utils.Timing where

import Formatting
import Formatting.Clock
import System.Clock

timeItAll :: String -> IO a -> IO a
timeItAll str x = do
  startMono <- getTime Monotonic
  startProcessCPU <- getTime ProcessCPUTime
  r <- x
  endMono <- getTime Monotonic
  endProcessCPU <- getTime ProcessCPUTime
  fprint (string % " -- Mono clock: " % timeSpecs % "\n") str startMono endMono
  fprint (string % " -- CPU clock: " % timeSpecs % "\n") str startProcessCPU endProcessCPU
  return r
