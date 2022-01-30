module Grisette.Control.Monad.UnionM
  ( UnionM,
  )
where

import Grisette.Control.Monad.UnionMBase
import Grisette.Data.SymPrim

type UnionM = UnionMBase SymBool
