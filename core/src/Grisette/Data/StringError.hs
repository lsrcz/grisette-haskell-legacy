{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Grisette.Data.StringError where

import Grisette.Data.Class.Bool
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Data.Class.PrimWrapper

newtype StringError = StringError String deriving (Eq, Ord)

instance Show StringError where
  show (StringError str) = str

instance (SymBoolOp bool) => Mergeable bool StringError where
  mergeStrategy = OrderedStrategy id (\_ -> SimpleStrategy $ \_ t _ -> t)

instance (SymBoolOp bool) => SEq bool StringError where
  l ==~ r = conc $ l == r
