{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad.Trans
  ( mrgLift,
  )
where

import Control.Monad.Trans
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Control.Monad.Union

-- | 'lift' with 'Mergeable' knowledge propagation.
mrgLift ::
  forall bool t m a.
  (MonadUnion bool (t m), MonadTrans t, Monad m, Mergeable bool a) =>
  m a ->
  t m a
mrgLift v = withUnionSimpleMergeableU @bool $ merge $ lift v
