{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Control.Monad.Union.MonadMerge where
import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.ApplicativeMerge

class (Monad f, ApplicativeMerge bool f) => MonadMerge bool f where
  mrgReturn :: (Mergeable bool a) => a -> f a
  (>>=~) :: (Mergeable bool b) => f a -> (a -> f b) -> f b
