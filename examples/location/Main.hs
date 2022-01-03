{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad.Except (ExceptT)
-- You can control whether the exception are bundled with locations by importing Exception/ExceptionWithLocation
-- They have the same APIs
-- import Exception
import ExceptionWithLocation
import GHC.Generics
import Grisette.Control.Monad.UnionM (UnionM)
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable

data RawException
  = Error1
  | Error2
  deriving (Show, Generic)

instance (SymBoolOp bool) => Mergeable bool RawException

x :: ExceptT (Exception RawException) UnionM ()
x = $assertWithException Error1 (ssymb "x")

y :: ExceptT (Exception RawException) UnionM ()
y = $assertWithException Error1 (ssymb "y")

main :: IO ()
main = do
  print x
  print $ mrgGuard (ssymb "a") x y
  print $ mrgGuard (ssymb "a") x x
