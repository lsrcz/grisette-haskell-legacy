module Grisette.Data.Class.SimpleMergeable (SimpleMergeable) where

import {-# SOURCE #-} Grisette.Data.Class.Mergeable

class Mergeable bool a => SimpleMergeable bool a where
  mrgIte :: bool -> a -> a -> a