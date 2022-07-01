module Litmus where

import Grisette
import Lang

data Litmus conc fs = Litmus
  { bound :: Integer,
    makeFs :: conc,
    setup :: [SysCall],
    test :: [SysCall],
    allow :: fs -> fs -> SymBool
  }
