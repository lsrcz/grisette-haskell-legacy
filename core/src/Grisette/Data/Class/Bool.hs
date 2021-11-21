{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Grisette.Data.Class.Bool (
  GeneralGEq(..),
  (/=~),
  LogicalOp(..),
  SymBoolOp
)where

class (SymBoolOp b) => GeneralGEq a b | a -> b where
  (==~) :: a -> a -> b
  infix 4 ==~

(/=~) :: (GeneralGEq a b) => a -> a -> b
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

class (GeneralGEq b b, Eq b, LogicalOp b) => SymBoolOp b where

