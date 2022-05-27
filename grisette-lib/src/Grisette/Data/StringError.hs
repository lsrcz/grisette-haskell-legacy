{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Grisette.Data.StringError
  ( StringError (..),
  )
where

import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym

newtype StringError = StringError String deriving (Eq, Ord)

instance Show StringError where
  show (StringError str) = str

instance (SymBoolOp bool) => Mergeable bool StringError where
  mergeStrategy = OrderedStrategy (\(StringError s) -> s) (\_ -> SimpleStrategy $ \_ t _ -> t)

instance (SymBoolOp bool) => SEq bool StringError where
  l ==~ r = conc $ l == r

instance TransformError ArithException StringError where
  transformError = StringError . show

instance ToSym StringError StringError where
  toSym = id

instance ToCon StringError StringError where
  toCon = Just
