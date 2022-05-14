module Grisette.Control.Monad.Except
  ( mrgThrowError,
    mrgCatchError,
  )
where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Control.Monad.Union

mrgThrowError :: (SymBoolOp bool, MonadError e m, MonadUnion bool m, Mergeable bool e, Mergeable bool a) => e -> m a
mrgThrowError = merge . throwError

mrgCatchError ::
  (SymBoolOp bool, MonadError e m, MonadUnion bool m, Mergeable bool e, Mergeable bool a) =>
  m a ->
  (e -> m a) ->
  m a
mrgCatchError v handler = merge $ v `catchError` (merge . handler)
