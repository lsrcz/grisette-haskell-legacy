{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.SymBool
  ( SymBool (..),
  )
where

import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.SymEval
import Grisette.Data.Prim.Model
import Grisette.Data.SymPrim

newtype SymBool = SymBool (Term Bool) deriving (Eq)

instance SymPrimType Bool where
  type SymPrim Bool = SymBool
  underlyingTerm (SymBool v) = v
  wrapTerm = SymBool

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
  ssymb = SymBool . ssymbTerm
  isymb i str = SymBool $ isymbTerm i str

instance Mergeable SymBool SymBool where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable SymBool SymBool where
  mrgIf = ites

instance ToSym Bool SymBool where
  toSym = conc

instance ToSym SymBool SymBool where
  toSym = id

instance ToCon SymBool SymBool where
  toCon = Just

instance ToCon SymBool Bool where
  toCon (SymBool (BoolConcTerm t)) = Just t
  toCon _ = Nothing

instance SymEval Model SymBool where
  symeval fillDefault model (SymBool t) = SymBool $ evaluateTerm fillDefault model t
