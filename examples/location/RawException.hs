{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
module RawException where
import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable

data RawException
  = Error1
  | Error2
  deriving (Show, Generic)

instance (SymBoolOp bool) => Mergeable bool RawException where

