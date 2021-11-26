{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.SymTabularFunc where

import Data.HashSet as S
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.FiniteFunction
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.SymPrim
import Grisette.Data.TabularFunc

newtype a =~> b = SymTabularFunc (Sym (a =-> b))

instance (SupportedPrim a, SupportedPrim b) => FiniteFunction (a =~> b) where
  type Arg (a =~> b) = Sym a
  type Ret (a =~> b) = Sym b
  runFunc (SymTabularFunc (Sym f)) t = Sym $ applyf f (underlyingTerm t)

instance (SupportedPrim a, SupportedPrim b) => PrimWrapper (a =~> b) (a =-> b) where
  conc = SymTabularFunc . Sym . concTerm
  concView (SymTabularFunc (Sym (TabularFuncConcTerm t))) = Just t
  concView _ = Nothing
  ssymb = SymTabularFunc . Sym . ssymbTerm
  isymb i str = SymTabularFunc $ Sym $ isymbTerm i str

instance
  ( SupportedPrim a,
    SupportedPrim b,
    ExtractSymbolics (S.HashSet TermSymbol) a,
    ExtractSymbolics (S.HashSet TermSymbol) b
  ) =>
  ExtractSymbolics (S.HashSet TermSymbol) (a =~> b)
  where
  extractSymbolics (SymTabularFunc (Sym t)) = extractSymbolicsTerm t
