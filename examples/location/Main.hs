{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad.Except (ExceptT)
-- You can control whether the exception are bundled with locations by importing Exception/ExceptionWithLocation
-- They have the same APIs
-- import Exception
import ExceptionWithLocation
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term

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
