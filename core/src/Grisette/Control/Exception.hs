{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
module Grisette.Control.Exception where

import Grisette.Data.Class.Error
import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.SimpleMergeable
import GHC.Generics
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym

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
  deriving (Show, Eq, Ord, Generic)

instance (SymBoolOp bool) => Mergeable bool VerificationConditions

instance (SymBoolOp bool) => SEq bool VerificationConditions

instance ToCon VerificationConditions VerificationConditions

instance ToSym VerificationConditions VerificationConditions

instance TransformError AssertionError VerificationConditions where
  transformError _ = AssertionViolation

gassert :: (TransformError AssertionError to, MonadError to erm, SymBoolOp bool, UnionMOp bool erm) => bool -> erm ()
gassert = gassertWithError AssertionError
