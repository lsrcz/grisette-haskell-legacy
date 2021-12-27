module Grisette.Data.Functor (mrgFmap) where

import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable

mrgFmap :: (UnionMOp bool f, Mergeable bool b, Functor f) => (a -> b) -> f a -> f b
mrgFmap f a = merge $ fmap f a
