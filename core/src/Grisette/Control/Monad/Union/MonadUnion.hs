{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Control.Monad.Union.MonadUnion where
import Grisette.Control.Monad.Union.MonadMerge
import Grisette.Control.Monad.Union.Mergeable

class (MonadMerge bool u) => MonadUnion bool u where
  mrgIf :: (Mergeable bool a) => bool -> u a -> u a -> u a

{-
instance {-# OVERLAPPABLE #-} (MonadUnion bool u, Mergeable bool a) => Mergeable bool (u a) where
  mergeStrategy = SimpleStrategy mrgIf
  -}
