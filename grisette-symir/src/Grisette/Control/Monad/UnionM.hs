module Grisette.Control.Monad.UnionM
  ( UnionM,
  )
where

import Grisette.Core.Control.Monad.UnionMBase
import Grisette.Data.SymPrim

type UnionM = UnionMBase SymBool
