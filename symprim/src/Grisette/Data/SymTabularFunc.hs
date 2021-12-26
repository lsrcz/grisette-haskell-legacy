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
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.SymPrim
import Grisette.Data.TabularFunc

type a =~> b = Sym (a =-> b)

instance (SupportedPrim a, SupportedPrim b) => FiniteFunction (a =~> b) where
  type Arg (a =~> b) = Sym a
  type Ret (a =~> b) = Sym b
  runFunc (Sym f) t = Sym $ applyf f (underlyingTerm t)

instance (SupportedPrim a, SupportedPrim b) => Show (a =~> b) where
  show (Sym f) = pformat f

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
