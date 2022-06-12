{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Lib.Control.Monad.Trans
  ( mrgLift,
  )
where

import Control.Monad.Trans
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.Core.Control.Monad.Union

-- | 'lift' with 'Mergeable' knowledge propagation.
mrgLift ::
  forall bool t m a.
  (MonadUnion bool (t m), MonadTrans t, Monad m, Mergeable bool a) =>
  m a ->
  t m a
mrgLift v = merge $ lift v
