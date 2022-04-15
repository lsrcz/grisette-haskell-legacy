module Grisette.Data.Class.Error
  ( TransformError (..),
    gthrowError,
    gassertWithError,
  )
where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Control.Monad

-- | This class indicates error type @to@ can always represent the error type @from@.
class TransformError from to where
  -- | Transforms an error with type @from@ to an error with type @to@.
  transformError :: from -> to

instance {-# OVERLAPPABLE #-} TransformError a a where
  transformError = id

instance {-# OVERLAPS #-} TransformError a () where
  transformError _ = ()

instance {-# OVERLAPPING #-} TransformError () () where
  transformError _ = ()

-- | Used within a monadic multi path computation to begin exception processing.
--
-- Terminate the current execution path with the specified error.
gthrowError :: (TransformError from to, MonadError to erm) => from -> erm a
gthrowError = throwError . transformError

-- | Used within a monadic multi path computation for exception processing.
--
-- Terminate the current execution path with the specified error if the condition does not hold.
gassertWithError ::
  (TransformError from to, MonadError to erm, SymBoolOp bool, MonadUnion bool erm) =>
  from ->
  bool ->
  erm ()
gassertWithError err cond = mrgIf cond (return ()) (gthrowError err)
