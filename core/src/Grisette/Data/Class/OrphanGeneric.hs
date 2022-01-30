{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Data.Class.OrphanGeneric () where

import Control.Monad.Coroutine.SuspensionFunctors
import GHC.Generics

deriving instance Generic (Yield x y)

deriving instance Generic (Await x y)

deriving instance Generic (Request req res x)
