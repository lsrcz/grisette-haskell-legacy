module Grisette.Data.Class.SimpleMergeable (SimpleMergeable) where

import {-# SOURCE #-} Grisette.Data.Class.Mergeable
import GHC.Generics

class SimpleMergeable' bool f where
  mrgIte' :: bool -> f a -> f a -> f a

class Mergeable bool a => SimpleMergeable bool a where
  mrgIte :: bool -> a -> a -> a
  default mrgIte :: (Generic a, SimpleMergeable' bool (Rep a)) => bool -> a -> a -> a
  mrgIte cond t f = to $ mrgIte' cond (from t) (from f)