{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Integer
  ( ArithException (..),
    SignedDivMod (..),
    UnsignedDivMod (..),
    SignedQuotRem (..),
    SymIntegerOp,
  )
where

import Control.Exception
import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Control.Monad

-- | Safe signed 'div' and 'mod' with monadic error handling in multi-path execution.
class SignedDivMod bool a where
  divs :: (MonadError e uf, MonadUnion bool uf, TransformError ArithException e) => a -> a -> uf a
  mods :: (MonadError e uf, MonadUnion bool uf, TransformError ArithException e) => a -> a -> uf a

-- | Safe unsigned 'div' and 'mod' with monadic error handling in multi-path execution.
class UnsignedDivMod bool a where
  udivs :: (MonadError e uf, MonadUnion bool uf, TransformError ArithException e) => a -> a -> uf a
  umods :: (MonadError e uf, MonadUnion bool uf, TransformError ArithException e) => a -> a -> uf a

-- | Safe signed 'quot' and 'rem' with monadic error handling in multi-path execution.
class SignedQuotRem bool a where
  quots :: (MonadError e uf, MonadUnion bool uf, TransformError ArithException e) => a -> a -> uf a
  rems :: (MonadError e uf, MonadUnion bool uf, TransformError ArithException e) => a -> a -> uf a

-- | Aggregation for the operations on symbolic integer types
class (Num a, SEq bool a, SOrd bool a, PrimWrapper a Integer) => SymIntegerOp bool a
