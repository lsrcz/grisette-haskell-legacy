{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grisette.Data.SymPrim
  ( Sym (..),
    SymConcView (..),
    pattern SymConc,
    SymBool,
    SymInteger,
    type (=~>),
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.HashSet as S
import Data.Hashable
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.FiniteFunction
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.TabularFunc

newtype Sym a = Sym {underlyingTerm :: Term a}

class SupportedPrim a => SymConcView a where
  symConcView :: Sym a -> Maybe a

pattern SymConc :: SymConcView a => a -> Sym a
pattern SymConc c <-
  (Sym (ConcTerm _ c))
  where
    SymConc c = conc c

instance (SupportedPrim a) => ITEOp (Sym Bool) (Sym a) where
  ites (Sym c) (Sym t) (Sym f) = Sym $ iteterm c t f

instance (SupportedPrim a) => Mergeable (Sym Bool) (Sym a) where
  mergeStrategy = SimpleStrategy ites

instance (SupportedPrim a) => SimpleMergeable (Sym Bool) (Sym a) where
  mrgIf = ites

instance (SymConcView a) => PrimWrapper (Sym a) a where
  conc = Sym . concTerm
  ssymb = Sym . ssymbTerm
  isymb i str = Sym $ isymbTerm i str
  concView (SymConc t) = Just t
  concView _ = Nothing

instance (SupportedPrim a) => ToSym (Sym a) (Sym a) where
  toSym = id

instance (SymConcView a) => ToSym a (Sym a) where
  toSym = conc

instance (SupportedPrim a) => ToCon (Sym a) (Sym a) where
  toCon = Just

instance (SymConcView a) => ToCon (Sym a) a where
  toCon = symConcView

instance (SupportedPrim a) => SymEval Model (Sym a) where
  symeval fillDefault model (Sym t) = Sym $ evaluateTerm fillDefault model t

instance (SupportedPrim a) => ExtractSymbolics (S.HashSet TermSymbol) (Sym a) where
  extractSymbolics (Sym t) = extractSymbolicsTerm t

instance (SymBoolOp (Sym Bool), SupportedPrim a, SymConcView a) => SymGen (Sym Bool) () (Sym a) where
  genSymIndexed _ = mrgSingle <$> genSymSimpleIndexed @(Sym Bool) ()

instance (SymBoolOp (Sym Bool), SupportedPrim a, SymConcView a) => SymGenSimple (Sym Bool) () (Sym a) where
  genSymSimpleIndexed _ = do
    (i, s) <- get
    put (i + 1, s)
    return $ isymb i s

instance (SupportedPrim a) => Show (Sym a) where
  show (Sym t) = pformat t

instance (SupportedPrim a) => Hashable (Sym a) where
  hashWithSalt s (Sym v) = s `hashWithSalt` v

instance (SupportedPrim a) => Eq (Sym a) where
  (Sym l) == (Sym r) = l == r

type SymBool = Sym Bool

instance SEq (Sym Bool) (Sym Bool) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance LogicalOp (Sym Bool) where
  (Sym l) ||~ (Sym r) = Sym $ orb l r
  (Sym l) &&~ (Sym r) = Sym $ andb l r
  nots (Sym v) = Sym $ notb v

instance SymBoolOp (Sym Bool)

instance SymConcView Bool where
  symConcView (Sym (BoolConcTerm t)) = Just t
  symConcView _ = Nothing

type SymInteger = Sym Integer

instance SEq (Sym Bool) (Sym Integer) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance Num (Sym Integer) where
  (Sym l) + (Sym r) = Sym $ addi l r
  (Sym l) - (Sym r) = Sym $ minusi l r
  (Sym l) * (Sym r) = Sym $ timesi l r
  negate (Sym v) = Sym $ uminusi v
  abs (Sym v) = Sym $ absi v
  signum (Sym v) = Sym $ signumi v
  fromInteger i = conc i

instance SymConcView Integer where
  symConcView (Sym (IntegerConcTerm t)) = Just t
  symConcView _ = Nothing

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

type a =~> b = Sym (a =-> b)

instance (SupportedPrim a, SupportedPrim b) => FiniteFunction (a =~> b) where
  type Arg (a =~> b) = Sym a
  type Ret (a =~> b) = Sym b
  runFunc (Sym f) t = Sym $ applyf f (underlyingTerm t)

instance (SupportedPrim a, SupportedPrim b) => SymConcView (a =-> b) where
  symConcView (Sym (TabularFuncConcTerm t)) = Just t
  symConcView _ = Nothing

instance
  ( SupportedPrim a,
    SupportedPrim b,
    ExtractSymbolics (S.HashSet TermSymbol) a,
    ExtractSymbolics (S.HashSet TermSymbol) b
  ) =>
  ExtractSymbolics (S.HashSet TermSymbol) (a =~> b)
  where
  extractSymbolics (Sym t) = extractSymbolicsTerm t
