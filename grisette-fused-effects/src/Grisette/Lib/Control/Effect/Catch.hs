module Grisette.Lib.Control.Effect.Catch where

import Control.Effect.Catch
import Grisette.Core

mrgCatchError ::
  (Has (Catch e) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) =>
  m a ->
  (e -> m a) ->
  m a
mrgCatchError m h = merge $ catchError m h
