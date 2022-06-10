module Grisette.Lib.Control.Effect.State where

import Control.Effect.State
import Grisette.Core

mrgGet :: (Has (State s) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool s) => m s
mrgGet = merge get

mrgGets :: (Has (State s) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) => (s -> a) -> m a
mrgGets = merge . gets

mrgPut :: (Has (State s) sig m, SymBoolOp bool, UnionLike bool m) => s -> m ()
mrgPut = merge . put

mrgModify :: (Has (State s) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool s) => (s -> s) -> m ()
mrgModify f = do
  a <- mrgGet
  mrgPut $! f a

mrgModifyLazy :: (Has (State s) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool s) => (s -> s) -> m ()
mrgModifyLazy f = mrgGet >>= mrgPut . f

mrgState :: (Has (State s) sig m, SymBoolOp bool, UnionLike bool m, Mergeable bool a) => (s -> (s, a)) -> m a
mrgState = merge . state

