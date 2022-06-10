module Grisette.Lib.Control.Effect.Reader where
import Control.Effect.Reader
import Grisette.Core

mrgAsk :: (Has (Reader r) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool r) => m r
mrgAsk = merge ask

mrgAsks :: (Has (Reader r) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) => (r -> a) -> m a
mrgAsks = merge . asks

mrgLocal :: (Has (Reader r) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) => (r -> r) -> m a -> m a
mrgLocal f = merge . local f
