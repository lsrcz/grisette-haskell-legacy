{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad.Trans where

import Control.Monad.Trans
import Grisette.Control.Monad.Union.Mergeable

mrgLift ::
  forall bool t m a.
  (StrongSimpleMergeable1 bool (t m), MonadTrans t, Monad m, Mergeable bool a) =>
  m a ->
  t m a
mrgLift = withStrongSimpleMergeable @bool @(t m) @a $ merge @bool . lift
