{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm (SomeTerm (..)) where

import Data.Hashable
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils

data SomeTerm where
  SomeTerm :: forall a. (SupportedPrim a) => Term a -> SomeTerm

instance Eq SomeTerm where
  (SomeTerm t1) == (SomeTerm t2) = identityWithTypeRep t1 == identityWithTypeRep t2

instance Hashable SomeTerm where
  hashWithSalt s (SomeTerm t) = hashWithSalt s $ identityWithTypeRep t

instance Show SomeTerm where
  show (SomeTerm t) = show t
