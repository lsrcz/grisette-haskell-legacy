{-# LANGUAGE MultiParamTypeClasses #-}

module Grisette.Data.SymInt where

import Grisette.Control.Monad.Union.Mergeable
import Grisette.Control.Monad.Union.MonadUnion
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Int
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.SymBool
import Grisette.Prim.Bool
import Grisette.Prim.Integer
import Grisette.Prim.InternedTerm
import Control.Monad.Except
import Grisette.Control.Monad.Union.MonadMerge

newtype SymInteger = SymInteger (Term Integer) deriving (Eq)

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
  concView (SymInteger (IntConcTerm t)) = Just t
  concView _ = Nothing
  symb = SymInteger . symbTerm

instance ITEOp SymBool SymInteger where
  ites (SymBool c) (SymInteger t) (SymInteger f) = SymInteger $ iteterm c t f

instance Mergeable SymBool SymInteger where
  mergeStrategy = SimpleStrategy ites

instance SignedDivMod SymBool SymInteger where
  divs (SymInteger l) rs@(SymInteger r) =
    mrgIf (rs ==~ conc 0) (throwError $ transformError DivByZeroError) (mrgReturn $ SymInteger $ divi l r)
  mods (SymInteger l) rs@(SymInteger r) =
    mrgIf (rs ==~ conc 0) (throwError $ transformError DivByZeroError) (mrgReturn $ SymInteger $ modi l r)

