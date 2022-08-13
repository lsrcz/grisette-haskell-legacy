{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
  ( SupportedPrim (..),
    UnaryOp (..),
    BinaryOp (..),
    TernaryOp (..),
    Symbol (..),
    TermSymbol (..),
    Term (..),
    UTerm (..),
  )
where

import Control.DeepSeq
import Data.Hashable
import Data.Interned
import Data.Kind
import Data.Typeable
import Grisette.IR.SymPrim.Data.Prim.ModelValue
import Language.Haskell.TH.Syntax

class (Lift t, Typeable t, Hashable t, Eq t, Show t, NFData t) => SupportedPrim t where
  type PrimConstraint t :: Constraint
  type PrimConstraint t = ()
  default withPrim :: PrimConstraint t => proxy t -> (PrimConstraint t => a) -> a
  withPrim :: proxy t -> (PrimConstraint t => a) -> a
  withPrim _ i = i
  termCache :: Cache (Term t)
  termCache = typeMemoizedCache

  -- termReverseCache :: ReverseCache (Term t)
  -- termReverseCache = typeMemoizedReverseCache
  pformatConc :: t -> String
  default pformatConc :: (Show t) => t -> String
  pformatConc = show
  pformatSymb :: proxy t -> Symbol -> String
  pformatSymb _ = show
  defaultValue :: t
  defaultValueDynamic :: proxy t -> ModelValue
  defaultValueDynamic _ = toModelValue (defaultValue @t)

class
  (SupportedPrim arg, SupportedPrim t, Lift tag, NFData tag, Show tag, Typeable tag, Eq tag, Hashable tag) =>
  UnaryOp tag arg t
    | tag arg -> t
  where
  partialEvalUnary :: (Typeable tag, Typeable t) => tag -> Term arg -> Term t
  pformatUnary :: tag -> Term arg -> String

class
  (SupportedPrim arg1, SupportedPrim arg2, SupportedPrim t, Lift tag, NFData tag, Show tag, Typeable tag, Eq tag, Hashable tag) =>
  BinaryOp tag arg1 arg2 t
    | tag arg1 arg2 -> t
  where
  partialEvalBinary :: (Typeable tag, Typeable t) => tag -> Term arg1 -> Term arg2 -> Term t
  pformatBinary :: tag -> Term arg1 -> Term arg2 -> String

class
  ( SupportedPrim arg1,
    SupportedPrim arg2,
    SupportedPrim arg3,
    SupportedPrim t,
    Lift tag,
    NFData tag,
    Show tag,
    Typeable tag,
    Eq tag,
    Hashable tag
  ) =>
  TernaryOp tag arg1 arg2 arg3 t
    | tag arg1 arg2 arg3 -> t
  where
  partialEvalTernary :: (Typeable tag, Typeable t) => tag -> Term arg1 -> Term arg2 -> Term arg3 -> Term t
  pformatTernary :: tag -> Term arg1 -> Term arg2 -> Term arg3 -> String

data Symbol where
  SimpleSymbol :: String -> Symbol
  IndexedSymbol :: String -> Int -> Symbol
  WithInfo :: forall a. (Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => Symbol -> a -> Symbol

data TermSymbol where
  TermSymbol :: forall t. (SupportedPrim t) => Proxy t -> Symbol -> TermSymbol

data Term t where
  ConcTerm :: (SupportedPrim t) => {-# UNPACK #-} !Id -> !t -> Term t
  SymbTerm :: (SupportedPrim t) => {-# UNPACK #-} !Id -> !TermSymbol -> Term t
  UnaryTerm ::
    (UnaryOp tag arg t) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg) ->
    Term t
  BinaryTerm ::
    (BinaryOp tag arg1 arg2 t) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    Term t
  TernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    !(Term arg3) ->
    Term t
  NotTerm :: {-# UNPACK #-} !Id -> !(Term Bool) -> Term Bool
  OrTerm :: {-# UNPACK #-} !Id -> !(Term Bool) -> !(Term Bool) -> Term Bool
  AndTerm :: {-# UNPACK #-} !Id -> !(Term Bool) -> !(Term Bool) -> Term Bool

data UTerm t where
  UConcTerm :: (SupportedPrim t) => !t -> UTerm t
  USymbTerm :: (SupportedPrim t) => !TermSymbol -> UTerm t
  UUnaryTerm :: (UnaryOp tag arg t) => !tag -> !(Term arg) -> UTerm t
  UBinaryTerm ::
    (BinaryOp tag arg1 arg2 t) =>
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    UTerm t
  UTernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t) =>
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    !(Term arg3) ->
    UTerm t
  UNotTerm :: !(Term Bool) -> UTerm Bool
  UOrTerm :: !(Term Bool) -> !(Term Bool) -> UTerm Bool
  UAndTerm :: !(Term Bool) -> !(Term Bool) -> UTerm Bool
