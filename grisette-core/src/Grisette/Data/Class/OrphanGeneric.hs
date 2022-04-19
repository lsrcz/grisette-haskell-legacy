{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Data.Class.OrphanGeneric () where

import Control.Monad.Coroutine.SuspensionFunctors
import GHC.Generics

deriving instance Generic (Yield x y)

deriving instance Generic (Await x y)

deriving instance Generic (Request req res x)

deriving instance Generic1 (Yield x)

deriving instance Generic1 (Await x)

deriving instance Generic1 (Request req res)