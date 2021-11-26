{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.SymBool
  ( SymBool,
  )
where

import Data.HashSet as S
import Data.Hashable
import Grisette.Data.Class.Bool
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model
import Grisette.Data.SymPrim

type SymBool = Sym Bool

instance Show (Sym Bool) where
  show (Sym t) = pformat t

instance SEq (Sym Bool) (Sym Bool) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance LogicalOp (Sym Bool) where
  (Sym l) ||~ (Sym r) = Sym $ orb l r
  (Sym l) &&~ (Sym r) = Sym $ andb l r
  nots (Sym v) = Sym $ notb v

instance ITEOp (Sym Bool) (Sym Bool) where
  ites (Sym c) (Sym t) (Sym f) = Sym $ iteterm c t f

instance Eq (Sym Bool) where
  (Sym l) == (Sym r) = l == r

instance Hashable (Sym Bool) where
  hashWithSalt s (Sym v) = s `hashWithSalt` v

instance SymBoolOp (Sym Bool)

instance PrimWrapper (Sym Bool) Bool where
  conc = Sym . concTerm
  concView (Sym (BoolConcTerm t)) = Just t
  concView _ = Nothing
  ssymb = Sym . ssymbTerm
  isymb i str = Sym $ isymbTerm i str

instance Mergeable (Sym Bool) (Sym Bool) where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable (Sym Bool) (Sym Bool) where
  mrgIf = ites

instance ToSym Bool (Sym Bool) where
  toSym = conc

instance ToSym (Sym Bool) (Sym Bool) where
  toSym = id

instance ToCon (Sym Bool) (Sym Bool) where
  toCon = Just

instance ToCon (Sym Bool) Bool where
  toCon (Sym (BoolConcTerm t)) = Just t
  toCon _ = Nothing

instance SymEval Model (Sym Bool) where
  symeval fillDefault model (Sym t) = Sym $ evaluateTerm fillDefault model t

instance ExtractSymbolics (S.HashSet TermSymbol) (Sym Bool) where
  extractSymbolics (Sym t) = extractSymbolicsTerm t
