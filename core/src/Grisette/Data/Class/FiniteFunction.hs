module Grisette.Data.Class.FiniteFunction
  ( FiniteFunction (..),
  )
where

class FiniteFunction f where
  type Arg f
  type Ret f
  runFunc :: f -> Arg f -> Ret f
