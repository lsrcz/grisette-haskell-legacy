module Grisette.Lib.Control.Monad.Except
  ( mrgThrowError,
    mrgCatchError,
  )
where

import Control.Monad.Except
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.Core.Control.Monad.Union

-- | 'throwError' with 'Mergeable' knowledge propagation.
mrgThrowError :: (SymBoolOp bool, MonadError e m, MonadUnion bool m, Mergeable bool a) => e -> m a
mrgThrowError = merge . throwError

-- | 'catchError' with 'Mergeable' knowledge propagation.
mrgCatchError ::
  (SymBoolOp bool, MonadError e m, MonadUnion bool m, Mergeable bool a) =>
  m a ->
  (e -> m a) ->
  m a
mrgCatchError v handler = merge $ v `catchError` (merge . handler)
