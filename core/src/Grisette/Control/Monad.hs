{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad where

import Grisette.Control.Monad.Union.Mergeable

mrgReturn :: forall bool m a. (StrongSimpleMergeable1 bool m, Mergeable bool a, Monad m) => a -> m a
mrgReturn v = withStrongSimpleMergeable' @bool $ merge @bool . return $ v

(>>=~) :: forall bool m a b. (StrongSimpleMergeable1 bool m, Mergeable bool b, Monad m) => m a -> (a -> m b) -> m b
a >>=~ f = withStrongSimpleMergeable' @bool $ merge @bool $ a >>= f
