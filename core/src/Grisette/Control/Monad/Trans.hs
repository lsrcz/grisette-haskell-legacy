{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Grisette.Control.Monad.Trans where
import Control.Monad.Trans
import Grisette.Control.Monad.Union.Mergeable

mrgLift :: forall t bool m a. (MonadTrans t, SimpleMergeable1 bool (t m), Monad m, Mergeable bool a) => m a -> t m a
mrgLift = withSimpleMergeable @bool @(t m) @a $ merge @bool . lift
