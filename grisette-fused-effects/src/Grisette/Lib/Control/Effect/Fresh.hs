module Grisette.Lib.Control.Effect.Fresh where
import Control.Effect.Fresh
import Grisette.Core

mrgFresh :: (Has Fresh sig m, SymBoolOp bool, UnionLike bool m) => m Int
mrgFresh = merge fresh
