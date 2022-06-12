module Grisette.Data.Union
  ( Union,
  )
where

import Grisette.Data.SymPrim
import Grisette.Core.Data.UnionBase

type Union = UnionBase SymBool
