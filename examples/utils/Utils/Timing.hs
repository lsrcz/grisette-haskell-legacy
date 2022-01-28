{-# LANGUAGE OverloadedStrings #-}
module Utils.Timing where

import System.Clock
import Formatting
import Formatting.Clock

timeItAll :: IO a -> IO a
timeItAll x = do
  startMono <- getTime Monotonic
  startProcessCPU <- getTime ProcessCPUTime
  r <- x
  endMono <- getTime Monotonic
  endProcessCPU <- getTime ProcessCPUTime
  fprint ("Mono clock: " % timeSpecs % "\n") startMono endMono
  fprint ("CPU clock: " % timeSpecs % "\n") startProcessCPU endProcessCPU
  return r
