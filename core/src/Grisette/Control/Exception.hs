{-# LANGUAGE DeriveAnyClass #-}
module Grisette.Control.Exception
  ( AssertionError (..),
    VerificationConditions (..),
    gassert,
  )
where

import Control.Monad.Except
import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Control.Exception
import Control.DeepSeq

data AssertionError = AssertionError
  deriving (Show, Eq, Ord, Generic)

instance (SymBoolOp bool) => Mergeable bool AssertionError

instance (SymBoolOp bool) => SimpleMergeable bool AssertionError

instance (SymBoolOp bool) => SEq bool AssertionError

instance ToCon AssertionError AssertionError

instance ToSym AssertionError AssertionError

data VerificationConditions
  = AssertionViolation
  | AssumptionViolation
  deriving (Show, Eq, Ord, Generic, NFData)

instance (SymBoolOp bool) => Mergeable bool VerificationConditions

instance (SymBoolOp bool) => SEq bool VerificationConditions

instance ToCon VerificationConditions VerificationConditions

instance ToSym VerificationConditions VerificationConditions

instance TransformError VerificationConditions VerificationConditions where
  transformError = id
instance TransformError AssertionError VerificationConditions where
  transformError _ = AssertionViolation

instance TransformError ArrayException AssertionError where
  transformError _ = AssertionError

instance TransformError AssertionError AssertionError where
  transformError = id

gassert :: (TransformError AssertionError to, MonadError to erm, SymBoolOp bool, UnionMOp bool erm) => bool -> erm ()
gassert = gassertWithError AssertionError
