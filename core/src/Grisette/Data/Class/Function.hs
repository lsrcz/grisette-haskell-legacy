module Grisette.Data.Class.Function
  ( Function (..),
  )
where

class Function f where
  type Arg f
  type Ret f
  (#) :: f -> Arg f -> Ret f
  infixl 9 #

instance Function (a -> b) where
  type Arg (a -> b) = a
  type Ret (a -> b) = b
  f # a = f a
