{-# LANGUAGE MultiParamTypeClasses #-}
module Grisette.Data.SymBool where

import Grisette.Prim.Bool
import Grisette.Prim.InternedTerm
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper

newtype SymBool = SymBool (Term Bool) deriving Eq

instance Show SymBool where
  show (SymBool t) = pformat t

instance GeneralGEq SymBool SymBool where
  (SymBool l) ==~ (SymBool r) = SymBool $ eqterm l r

instance LogicalOp SymBool where
  (SymBool l) ||~ (SymBool r) = SymBool $ orb l r
  (SymBool l) &&~ (SymBool r) = SymBool $ andb l r
  nots (SymBool v) = SymBool $ notb v

instance SymBoolOp SymBool

instance PrimWrapper SymBool Bool where
  conc = SymBool . concTerm
  symb = SymBool . symbTerm

concBool :: Bool -> SymBool
concBool = conc

symbBool :: String -> SymBool
symbBool = symb
