{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Grisette.Orphan.Either where

import Grisette.Data.Class.Bool
import Grisette.Control.Monad.Union.Mergeable

instance (SymBoolOp bool, Mergeable bool e, Mergeable bool a) => Mergeable bool (Either e a)

instance (SymBoolOp bool, Mergeable bool e) => Mergeable1 bool (Either e) where
  mergeStrategy1 = mergeStrategy

instance (SymBoolOp bool, SEq bool e, SEq bool a) => SEq bool (Either e a)

