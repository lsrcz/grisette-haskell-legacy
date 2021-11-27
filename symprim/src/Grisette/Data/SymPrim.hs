{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Data.SymPrim where

import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Class.Bool
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.SymEval
import Grisette.Data.Prim.Model
import Data.HashSet as S
import Grisette.Data.Class.SymGen
import Control.Monad.State

newtype Sym a = Sym {underlyingTerm :: Term a}

class SupportedPrim a => SymConcView a where
  symConcView :: Sym a -> Maybe a

pattern SymConc :: SymConcView a => a -> Sym a
pattern SymConc c <- (Sym (ConcTerm _ c))
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

