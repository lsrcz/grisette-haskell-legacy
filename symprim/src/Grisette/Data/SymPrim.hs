{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Grisette.Data.SymPrim where

import Grisette.Data.Prim.InternedTerm

newtype Sym a = Sym {underlyingTerm :: Term a}
