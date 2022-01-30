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
import Grisette.Data.Class.SimpleMergeable

class SignedDivMod bool a where
  divs :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a
  mods :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a

class UnsignedDivMod bool a where
  udivs :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a
  umods :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a

class SignedQuotRem bool a where
  quots :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a
  rems :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a

class (Num a, SEq bool a, SOrd bool a, PrimWrapper a Integer) => SymIntegerOp bool a
