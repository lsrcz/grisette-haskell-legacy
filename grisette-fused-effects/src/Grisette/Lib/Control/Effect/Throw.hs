module Grisette.Lib.Control.Effect.Throw where

import Control.Effect.Throw
import Grisette.Core

mrgThrowError :: (Has (Throw e) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) => e -> m a
mrgThrowError = merge . throwError

mrgLiftEither :: (Has (Throw e) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) => Either e a -> m a
mrgLiftEither = merge . liftEither
