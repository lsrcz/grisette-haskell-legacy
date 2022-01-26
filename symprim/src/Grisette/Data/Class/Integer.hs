{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Integer
  ( ArithException (..),
    SignedDivMod (..),
    UnsignedDivMod (..),
    SignedQuotRem (..),
    SymIntegerOp,
  )
where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.PrimWrapper
import Control.Exception

class SignedDivMod bool a where
  divs :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a
  mods :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a

class UnsignedDivMod bool a where
  udivs :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a
  umods :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a

class SignedQuotRem bool a where
  quots :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a
  rems :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithException e) => a -> a -> uf a

class (Num a, SEq bool a, SOrd bool a) => SymIntegerOp bool a
