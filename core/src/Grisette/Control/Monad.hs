{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad
  ( mrgReturn,
    (>>=~),
  )
where

import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable

mrgReturn :: forall bool m a. (UnionMOp bool m, Mergeable bool a, Monad m) => a -> m a
mrgReturn = withUnionMSimpleMergeableU . merge . return

(>>=~) :: forall bool m a b. (UnionMOp bool m, Mergeable bool b, Monad m) => m a -> (a -> m b) -> m b
a >>=~ f = withUnionMSimpleMergeableU $ merge $ a >>= f
