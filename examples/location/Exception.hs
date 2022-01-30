{-# LANGUAGE TemplateHaskell #-}

module Exception where

import Control.Monad.Except
import Grisette.Core
import Language.Haskell.TH

type Exception raw = raw

assertWithException :: Q Exp
assertWithException = [|assertWithException'|]

assertWithException' ::
  forall bool raw eu.
  (SymBoolOp bool, MonadError (Exception raw) eu, UnionMOp bool eu) =>
  raw ->
  bool ->
  eu ()
assertWithException' ex x = mrgGuard x (return ()) (throwError ex)
