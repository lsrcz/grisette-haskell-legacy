{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad.Trans where

import Control.Monad.Trans
import Grisette.Control.Monad.Union.Mergeable

mrgLift ::
  forall bool t m a.
  (UnionMOp bool (t m), MonadTrans t, Monad m, Mergeable bool a) =>
  m a ->
  t m a
mrgLift = withUnionMSimpleMergeableU . merge . lift 
