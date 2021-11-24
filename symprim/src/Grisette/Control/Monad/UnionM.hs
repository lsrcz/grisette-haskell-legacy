module Grisette.Control.Monad.UnionM (UnionM) where

import Grisette.Data.SymBool
import Grisette.Control.Monad.UnionMBase

type UnionM = UnionMBase SymBool
