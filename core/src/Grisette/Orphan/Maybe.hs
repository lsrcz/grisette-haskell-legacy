{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Grisette.Orphan.Maybe where
import Grisette.Data.Class.Bool
import Grisette.Control.Monad.Union.Mergeable

instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (Maybe a)

instance (SymBoolOp bool) => Mergeable1 bool Maybe where
  mergeStrategy1 = mergeStrategy

instance (SymBoolOp bool, SEq bool a) => SEq bool (Maybe a)

