module Grisette.Data.Class.Error
  ( TransformError (..),
    gthrowError,
    gassertWithError,
  )
where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Control.Monad

class TransformError from to where
  transformError :: from -> to

instance TransformError a () where
  transformError _ = ()

gthrowError :: (TransformError from to, MonadError to erm) => from -> erm a
gthrowError = throwError . transformError

gassertWithError ::
  (TransformError from to, MonadError to erm, SymBoolOp bool, MonadUnion bool erm) =>
  from ->
  bool ->
  erm ()
gassertWithError err cond = mrgIf cond (return ()) (gthrowError err)
