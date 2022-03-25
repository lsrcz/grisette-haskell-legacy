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
import Grisette.Control.Monad
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ExtractSymbolics

data AssertionError = AssertionError
  deriving (Show, Eq, Ord, Generic, NFData, ToCon AssertionError, ToSym AssertionError)

instance (SymBoolOp bool) => Mergeable bool AssertionError

instance (SymBoolOp bool) => SimpleMergeable bool AssertionError

instance (SymBoolOp bool) => SEq bool AssertionError

instance (SymBoolOp bool) => SOrd bool AssertionError where
  _ <=~ _ = conc True
  _ <~ _ = conc False
  _ >=~ _ = conc True
  _ >~ _ = conc False
  _ `symCompare` _ = mrgReturn EQ

instance SymEval a AssertionError where

instance (Monoid a) => ExtractSymbolics a AssertionError where

data VerificationConditions
  = AssertionViolation
  | AssumptionViolation
  deriving (Show, Eq, Ord, Generic, NFData, ToSym VerificationConditions, ToCon VerificationConditions)

instance (SymBoolOp bool) => Mergeable bool VerificationConditions

instance (SymBoolOp bool) => SEq bool VerificationConditions

instance (SymBoolOp bool) => SOrd bool VerificationConditions where
  l <=~ r = conc $ l <= r
  l <~ r = conc $ l < r
  l >=~ r = conc $ l >= r
  l >~ r = conc $ l > r
  l `symCompare` r = mrgReturn $ l `compare` r

instance SymEval a VerificationConditions where

instance (Monoid a) => ExtractSymbolics a VerificationConditions where

instance TransformError VerificationConditions VerificationConditions where
  transformError = id
instance TransformError AssertionError VerificationConditions where
  transformError _ = AssertionViolation

instance TransformError ArrayException AssertionError where
  transformError _ = AssertionError

instance TransformError AssertionError AssertionError where
  transformError = id

gassert :: (TransformError AssertionError to, MonadError to erm, SymBoolOp bool, MonadUnion bool erm) => bool -> erm ()
gassert = gassertWithError AssertionError
