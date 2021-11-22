{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Grisette.Data.Class.Int where

import Grisette.Data.Class.Error
import Control.Monad.Except
import Grisette.Control.Monad.Union.MonadUnion
import Grisette.Data.Class.Bool
import Grisette.Data.StringError

class LinearArithOp a where
  (+~) :: a -> a -> a
  (-~) :: a -> a -> a
  negs :: a -> a

class TimesOp a where
  (*~) :: a -> a -> a

data ArithError = DivByZeroError deriving Show

instance TransformError ArithError () where
  transformError _ = ()

instance TransformError ArithError StringError where
  transformError DivByZeroError = StringError "DivByZero"

class SignedDivMod bool a where
  divs :: (MonadError e uf, MonadUnion bool uf, TransformError ArithError e) => a -> a -> uf a
  mods :: (MonadError e uf, MonadUnion bool uf, TransformError ArithError e) => a -> a -> uf a

class UnsignedDivMod bool a where
  udivs :: (MonadError e uf, MonadUnion bool uf, TransformError ArithError e) => a -> a -> uf a
  umods :: (MonadError e uf, MonadUnion bool uf, TransformError ArithError e) => a -> a -> uf a

class SignedQuotRem bool a where
  quots :: (MonadError e uf, MonadUnion bool uf, TransformError ArithError e) => a -> a -> uf a
  rems :: (MonadError e uf, MonadUnion bool uf, TransformError ArithError e) => a -> a -> uf a

class (LinearArithOp a, TimesOp a, SEq bool a) => IntOp bool a where
