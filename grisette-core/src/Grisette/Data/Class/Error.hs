{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Grisette.Data.Class.Error
  ( TransformError (..),
    symThrowTransformableError,
    symFailIfNot,
  )
where

import Control.Monad.Except
import Grisette.Control.Monad
import Grisette.Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable

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
symThrowTransformableError ::
  ( SymBoolOp bool,
    Mergeable bool to,
    Mergeable bool a,
    TransformError from to,
    MonadError to erm,
    MonadUnion bool erm
  ) =>
  from ->
  erm a
symThrowTransformableError = mrgThrowError . transformError

-- | Used within a monadic multi path computation for exception processing.
--
-- Terminate the current execution path with the specified error if the condition does not hold.
symFailIfNot ::
  ( SymBoolOp bool,
    Mergeable bool to,
    TransformError from to,
    MonadError to erm,
    MonadUnion bool erm
  ) =>
  from ->
  bool ->
  erm ()
symFailIfNot err cond = mrgIf cond (return ()) (symThrowTransformableError err)
