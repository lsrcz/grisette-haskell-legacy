{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.SymInteger
  ( SymInteger,
  )
where

import Control.Monad.Except
import Data.HashSet as S
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model
import Grisette.Data.SymBool ()
import Grisette.Data.SymPrim

type SymInteger = Sym Integer

instance Show (Sym Integer) where
  show (Sym t) = pformat t

instance SEq (Sym Bool) (Sym Integer) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance LinearArithOp (Sym Integer) where
  (Sym l) +~ (Sym r) = Sym $ addi l r
  (Sym l) -~ (Sym r) = Sym $ minusi l r
  negs (Sym v) = Sym $ uminusi v

instance TimesOp (Sym Integer) where
  (Sym l) *~ (Sym r) = Sym $ timesi l r

instance PrimWrapper (Sym Integer) Integer where
  conc = Sym . concTerm
  concView (Sym (IntegerConcTerm t)) = Just t
  concView _ = Nothing
  ssymb = Sym . ssymbTerm
  isymb i str = Sym $ isymbTerm i str

instance ITEOp (Sym Bool) (Sym Integer) where
  ites (Sym c) (Sym t) (Sym f) = Sym $ iteterm c t f

instance Mergeable (Sym Bool) (Sym Integer) where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable (Sym Bool) (Sym Integer) where
  mrgIf = ites

instance SignedDivMod (Sym Bool) (Sym Integer) where
  divs (Sym l) rs@(Sym r) =
    withSimpleMergeableU @(Sym Bool) $
      mrgIf @(Sym Bool)
        (rs ==~ conc 0)
        (throwError $ transformError DivByZeroError)
        (mrgReturn $ Sym $ divi l r)
  mods (Sym l) rs@(Sym r) =
    withSimpleMergeableU @(Sym Bool) $
      mrgIf @(Sym Bool)
        (rs ==~ conc 0)
        (throwError $ transformError DivByZeroError)
        (mrgReturn $ Sym $ modi l r)

instance SymIntegerOp (Sym Bool) (Sym Integer)

instance ToSym Integer (Sym Integer) where
  toSym = conc

instance ToSym (Sym Integer) (Sym Integer) where
  toSym = id

instance ToCon (Sym Integer) (Sym Integer) where
  toCon = Just

instance ToCon (Sym Integer) Integer where
  toCon (Sym (IntegerConcTerm t)) = Just t
  toCon _ = Nothing

instance SymEval Model (Sym Integer) where
  symeval fillDefault model (Sym t) = Sym $ evaluateTerm fillDefault model t

instance ExtractSymbolics (S.HashSet TermSymbol) (Sym Integer) where
  extractSymbolics (Sym t) = extractSymbolicsTerm t
