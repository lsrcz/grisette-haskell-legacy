module Grisette.Control.Monad.Trans
  ( mrgLift,
  )
where

import Control.Monad.Trans
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable

mrgLift ::
  forall bool t m a.
  (UnionMOp bool (t m), MonadTrans t, Monad m, Mergeable bool a) =>
  m a ->
  t m a
mrgLift = withUnionMSimpleMergeableU . merge . lift
