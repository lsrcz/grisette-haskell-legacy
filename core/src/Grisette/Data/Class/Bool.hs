{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Bool
  ( SEq (..),
    SEq' (..),
    (/=~),
    LogicalOp (..),
    SymBoolOp,
    ITEOp (..),
  )
where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Generics.Deriving
import Grisette.Data.Class.PrimWrapper

class (SymBoolOp bool) => SEq' bool f where
  (==~~) :: f a -> f a -> bool
  infix 4 ==~~

instance (SymBoolOp bool) => SEq' bool U1 where
  _ ==~~ _ = conc True

instance (SymBoolOp bool) => SEq' bool V1 where
  _ ==~~ _ = conc True

instance (SymBoolOp bool, SEq bool c) => SEq' bool (K1 i c) where
  (K1 a) ==~~ (K1 b) = a ==~ b

instance (SymBoolOp bool, SEq' bool a) => SEq' bool (M1 i c a) where
  (M1 a) ==~~ (M1 b) = a ==~~ b

instance (SymBoolOp bool, SEq' bool a, SEq' bool b) => SEq' bool (a :+: b) where
  (L1 a) ==~~ (L1 b) = a ==~~ b
  (R1 a) ==~~ (R1 b) = a ==~~ b
  _ ==~~ _ = conc False

instance (SymBoolOp bool, SEq' bool a, SEq' bool b) => SEq' bool (a :*: b) where
  (a1 :*: b1) ==~~ (a2 :*: b2) = (a1 ==~~ a2) &&~ (b1 ==~~ b2)

class (SymBoolOp bool) => SEq bool a where
  (==~) :: a -> a -> bool
  infix 4 ==~
  default (==~) :: (Generic a, SEq' bool (Rep a)) => a -> a -> bool
  x ==~ y = from x ==~~ from y

(/=~) :: (SEq bool a) => a -> a -> bool
(/=~) l r = nots $ l ==~ r

infix 4 /=~

class LogicalOp b where
  (||~) :: b -> b -> b
  a ||~ b = nots $ nots a &&~ nots b
  infixr 2 ||~
  (&&~) :: b -> b -> b
  a &&~ b = nots $ nots a ||~ nots b
  infixr 3 &&~
  nots :: b -> b
  xors :: b -> b -> b
  a `xors` b = (a &&~ nots b) ||~ (nots a &&~ b)
  implies :: b -> b -> b
  a `implies` b = nots a ||~ b

class ITEOp b v where
  ites :: b -> v -> v -> v

class (SEq b b, Eq b, LogicalOp b, PrimWrapper b Bool, ITEOp b b) => SymBoolOp b

instance (SymBoolOp bool, SEq bool a) => SEq bool (Maybe a)

instance (SymBoolOp bool, SEq bool e, SEq bool a) => SEq bool (Either e a)

instance (SymBoolOp bool, SEq bool (m (Either e a))) => SEq bool (ExceptT e m a) where
  (ExceptT a) ==~ (ExceptT b) = a ==~ b

instance (SymBoolOp bool, SEq bool (m (Maybe a))) => SEq bool (MaybeT m a) where
  (MaybeT a) ==~ (MaybeT b) = a ==~ b
