{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Grisette.Data.Class.Error (TransformError (..), gthrowError, gassertWithError) where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.SimpleMergeable

class TransformError from to where
  transformError :: from -> to

instance TransformError a () where
  transformError _ = ()

gthrowError :: (TransformError from to, MonadError to erm) => from -> erm ()
gthrowError = throwError . transformError

gassertWithError ::
  (TransformError from to, MonadError to erm, SymBoolOp bool, UnionMOp bool erm) =>
  from ->
  bool ->
  erm ()
gassertWithError err cond = mrgGuard cond (return ()) (gthrowError err)
