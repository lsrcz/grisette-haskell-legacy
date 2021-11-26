{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances #-}

module Grisette.Data.SymInteger
  ( SymInteger (..),
  )
where

import Control.Monad.Except
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.SymBool
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.SymEval
import Grisette.Data.Prim.Model
import Grisette.Data.SymPrim
import Grisette.Data.Class.ExtractSymbolics
import Data.HashSet as S

newtype SymInteger = SymInteger (Term Integer) deriving (Eq)

instance SymPrimType Integer where
  type SymPrim Integer = SymInteger
  underlyingTerm (SymInteger v) = v
  wrapTerm = SymInteger

instance Show SymInteger where
  show (SymInteger t) = pformat t

instance SEq SymBool SymInteger where
  (SymInteger l) ==~ (SymInteger r) = SymBool $ eqterm l r

instance LinearArithOp SymInteger where
  (SymInteger l) +~ (SymInteger r) = SymInteger $ addi l r
  (SymInteger l) -~ (SymInteger r) = SymInteger $ minusi l r
  negs (SymInteger v) = SymInteger $ uminusi v

instance TimesOp SymInteger where
  (SymInteger l) *~ (SymInteger r) = SymInteger $ timesi l r

instance PrimWrapper SymInteger Integer where
  conc = SymInteger . concTerm
  concView (SymInteger (IntegerConcTerm t)) = Just t
  concView _ = Nothing
  ssymb = SymInteger . ssymbTerm
  isymb i str = SymInteger $ isymbTerm i str

instance ITEOp SymBool SymInteger where
  ites (SymBool c) (SymInteger t) (SymInteger f) = SymInteger $ iteterm c t f

instance Mergeable SymBool SymInteger where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable SymBool SymInteger where
  mrgIf = ites

instance SignedDivMod SymBool SymInteger where
  divs (SymInteger l) rs@(SymInteger r) =
    withSimpleMergeableU @SymBool $
      mrgIf @SymBool
        (rs ==~ conc 0)
        (throwError $ transformError DivByZeroError)
        (mrgReturn $ SymInteger $ divi l r)
  mods (SymInteger l) rs@(SymInteger r) =
    withSimpleMergeableU @SymBool $
      mrgIf @SymBool
        (rs ==~ conc 0)
        (throwError $ transformError DivByZeroError)
        (mrgReturn $ SymInteger $ modi l r)

instance SymIntegerOp SymBool SymInteger

instance ToSym Integer SymInteger where
  toSym = conc

instance ToSym SymInteger SymInteger where
  toSym = id

instance ToCon SymInteger SymInteger where
  toCon = Just

instance ToCon SymInteger Integer where
  toCon (SymInteger (IntegerConcTerm t)) = Just t
  toCon _ = Nothing

instance SymEval Model SymInteger where
  symeval fillDefault model (SymInteger t) = SymInteger $ evaluateTerm fillDefault model t

instance ExtractSymbolics (S.HashSet TermSymbol) SymInteger where
  extractSymbolics (SymInteger t) = extractSymbolicsTerm t
