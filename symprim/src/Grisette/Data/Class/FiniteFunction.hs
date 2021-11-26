{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
module Grisette.Data.Class.FiniteFunction where

class FiniteFunction f where
  type Arg f
  type Ret f
  runFunc :: f -> Arg f -> Ret f

