{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}

module Grisette.Data.Class.OrphanGeneric where
import GHC.Generics
import Control.Monad.Coroutine.SuspensionFunctors

deriving instance Generic (Yield x y)

deriving instance Generic (Await x y)

deriving instance Generic (Request req res x)


