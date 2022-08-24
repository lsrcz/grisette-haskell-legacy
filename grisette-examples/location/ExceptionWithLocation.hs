{-# LANGUAGE TemplateHaskell #-}

module ExceptionWithLocation where

import Control.Monad.Except
import qualified Data.ByteString.UTF8 as B
import Debug.Trace.LocationTH (__LOCATION__)
import GHC.Generics
import Grisette
import Language.Haskell.TH

data Exception raw = ExceptionWithLocation raw B.ByteString deriving (Show, Generic)

deriving via
  (Default (Exception raw))
  instance
    (SymBoolOp bool, Mergeable bool raw) => Mergeable bool (Exception raw)

exceptWithLocation :: Q Exp
exceptWithLocation = [|\e -> ExceptionWithLocation e (B.fromString $__LOCATION__)|]

assertWithException :: Q Exp
assertWithException = [|assertWithException' (B.fromString $__LOCATION__)|]

assertWithException' ::
  forall bool raw eu.
  (SymBoolOp bool, MonadError (Exception raw) eu, MonadUnion bool eu) =>
  B.ByteString ->
  raw ->
  bool ->
  eu ()
assertWithException' loc ex x = mrgIf x (return ()) (throwError $ ExceptionWithLocation ex loc)
