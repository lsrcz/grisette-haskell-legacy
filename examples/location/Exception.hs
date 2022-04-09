{-# LANGUAGE TemplateHaskell #-}

module Exception where

import Control.Monad.Except
import Grisette
import Language.Haskell.TH

type Exception raw = raw

assertWithException :: Q Exp
assertWithException = [|assertWithException'|]

assertWithException' ::
  forall bool raw eu.
  (SymBoolOp bool, MonadError (Exception raw) eu, MonadUnion bool eu) =>
  raw ->
  bool ->
  eu ()
assertWithException' ex x = mrgIf x (return ()) (throwError ex)
