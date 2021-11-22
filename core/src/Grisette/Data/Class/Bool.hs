{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
module Grisette.Data.Class.Bool (
  SEq(..),
  (/=~),
  LogicalOp(..),
  SymBoolOp,
  ITEOp(..)
)where
import Grisette.Data.Class.PrimWrapper
import Generics.Deriving

class (SymBoolOp bool) => SEq' bool f  where
  (==~~) :: f a -> f a -> bool
  infix 4 ==~~

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

class (SymBoolOp bool) => SEq bool a | a -> bool where
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

class (SEq b b, Eq b, LogicalOp b, PrimWrapper b Bool, ITEOp b b) => SymBoolOp b where

