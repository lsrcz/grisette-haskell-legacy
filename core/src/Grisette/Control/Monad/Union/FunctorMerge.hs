{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Control.Monad.Union.FunctorMerge where
import Grisette.Control.Monad.Union.Mergeable

class (Functor f, MergeableContainer bool f) => FunctorMerge bool f where
  mrgFmap :: (Mergeable bool b) => (a -> b) -> f a -> f b
