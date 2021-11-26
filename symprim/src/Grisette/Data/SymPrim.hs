{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module Grisette.Data.SymPrim where
import Grisette.Data.Prim.InternedTerm

class SymPrimType a where
  type SymPrim a
  underlyingTerm :: SymPrim a -> Term a
  wrapTerm :: Term a -> SymPrim a
