{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Grisette.Data.Class.FiniteFunction where

class FiniteFunction f a b | f -> a b where
  runFunc :: f -> a -> b

