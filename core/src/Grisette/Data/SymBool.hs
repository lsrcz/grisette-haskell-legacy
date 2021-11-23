{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
module Grisette.Data.SymBool where

import Grisette.Prim.Bool
import Grisette.Prim.InternedTerm
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper
import Grisette.Control.Monad.Union.Mergeable

newtype SymBool = SymBool (Term Bool) deriving Eq

instance Show SymBool where
  show (SymBool t) = pformat t

instance SEq SymBool SymBool where
  (SymBool l) ==~ (SymBool r) = SymBool $ eqterm l r

instance LogicalOp SymBool where
  (SymBool l) ||~ (SymBool r) = SymBool $ orb l r
  (SymBool l) &&~ (SymBool r) = SymBool $ andb l r
  nots (SymBool v) = SymBool $ notb v

instance ITEOp SymBool SymBool where
  ites (SymBool c) (SymBool t) (SymBool f) = SymBool $ iteterm c t f

instance SymBoolOp SymBool

instance PrimWrapper SymBool Bool where
  conc = SymBool . concTerm
  concView (SymBool (BoolConcTerm t)) = Just t
  concView _ = Nothing
  symb = SymBool . symbTerm

concBool :: Bool -> SymBool
concBool = conc

symbBool :: String -> SymBool
symbBool = symb

instance Mergeable SymBool SymBool where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable SymBool SymBool where
  mrgIf = ites
