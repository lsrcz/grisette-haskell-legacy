{-# LANGUAGE TemplateHaskell #-}
module Main where

import RawException
-- You can control whether the exception are bundled with locations by importing Exception/ExceptionWithLocation
-- They have the same APIs
import Exception
-- import ExceptionWithLocation
import Control.Monad.Except (ExceptT)
import Grisette.Control.Monad.UnionM (UnionM)
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable

x :: ExceptT Exception UnionM ()
x = $assertWithException Error1 (ssymb "x")

y :: ExceptT Exception UnionM ()
y = $assertWithException Error1 (ssymb "y")

main :: IO ()
main = do
  print x
  print $ mrgGuard (ssymb "a") x y
  print $ mrgGuard (ssymb "a") x x
