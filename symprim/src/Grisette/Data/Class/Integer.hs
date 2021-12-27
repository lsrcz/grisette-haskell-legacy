{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Integer
  ( ArithError (..),
    SignedDivMod (..),
    UnsignedDivMod (..),
    SignedQuotRem (..),
    SymIntegerOp,
  )
where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.SimpleMergeable

data ArithError = DivByZeroError deriving (Show)

instance TransformError ArithError () where
  transformError _ = ()

class SignedDivMod bool a where
  divs :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithError e) => a -> a -> uf a
  mods :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithError e) => a -> a -> uf a

class UnsignedDivMod bool a where
  udivs :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithError e) => a -> a -> uf a
  umods :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithError e) => a -> a -> uf a

class SignedQuotRem bool a where
  quots :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithError e) => a -> a -> uf a
  rems :: (MonadError e uf, Monad uf, UnionMOp bool uf, TransformError ArithError e) => a -> a -> uf a

class (Num a, SEq bool a) => SymIntegerOp bool a
