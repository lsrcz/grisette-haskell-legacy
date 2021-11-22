{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Grisette.Control.Monad where
import Grisette.Control.Monad.Union.Mergeable 

mrgReturn :: forall bool m a. (SimpleMergeable1 bool m, Mergeable bool a, Monad m) => a -> m a
mrgReturn v = withSimpleMergeable' @bool $ merge @bool . return $ v

(>>=~) :: forall bool m a b. (SimpleMergeable1 bool m, Mergeable bool b, Monad m) => m a -> (a -> m b) -> m b
a >>=~ f = withSimpleMergeable' @bool $ merge @bool $ a >>= f
