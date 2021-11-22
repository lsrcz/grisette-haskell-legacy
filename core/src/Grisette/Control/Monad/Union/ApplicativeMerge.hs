{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Control.Monad.Union.ApplicativeMerge where
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.FunctorMerge

class (Applicative f, FunctorMerge bool f) => ApplicativeMerge bool f where
  mrgPure :: (Mergeable bool a) => a -> f a
  (<*>~) :: (Mergeable bool b) => f (a -> b) -> f a -> f b
