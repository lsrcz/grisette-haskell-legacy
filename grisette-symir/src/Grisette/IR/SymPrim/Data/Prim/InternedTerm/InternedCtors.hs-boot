{-# LANGUAGE RankNTypes #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
  ( constructUnary,
    constructBinary,
    constructTernary,
    concTerm,
    symbTerm,
    ssymbTerm,
    isymbTerm,
    sinfosymbTerm,
    iinfosymbTerm,
    notTerm,
    orTerm,
    andTerm,
    eqvTerm,
    iteTerm,
    addNumTerm,
    uminusNumTerm,
    timesNumTerm,
    absNumTerm,
    signumNumTerm,
    ltNumTerm,
    leNumTerm,
  )
where

import Control.DeepSeq
import Data.Hashable
import Data.Typeable
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Language.Haskell.TH.Syntax

constructUnary ::
  forall tag arg t.
  (SupportedPrim t, UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg ->
  Term t
constructBinary ::
  forall tag arg1 arg2 t.
  (SupportedPrim t, BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term t
constructTernary ::
  forall tag arg1 arg2 arg3 t.
  (SupportedPrim t, TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term arg3 ->
  Term t
concTerm :: (SupportedPrim t, Typeable t, Hashable t, Eq t, Show t) => t -> Term t
symbTerm :: forall t. (SupportedPrim t, Typeable t) => Symbol -> Term t
ssymbTerm :: (SupportedPrim t, Typeable t) => String -> Term t
isymbTerm :: (SupportedPrim t, Typeable t) => String -> Int -> Term t
sinfosymbTerm :: (SupportedPrim t, Typeable t, Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> a -> Term t
iinfosymbTerm :: (SupportedPrim t, Typeable t, Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> Int -> a -> Term t
notTerm :: Term Bool -> Term Bool
orTerm :: Term Bool -> Term Bool -> Term Bool
andTerm :: Term Bool -> Term Bool -> Term Bool
eqvTerm :: SupportedPrim a => Term a -> Term a -> Term Bool
iteTerm :: SupportedPrim a => Term Bool -> Term a -> Term a -> Term a
addNumTerm :: (SupportedPrim a, Num a) => Term a -> Term a -> Term a
uminusNumTerm :: (SupportedPrim a, Num a) => Term a -> Term a
timesNumTerm :: (SupportedPrim a, Num a) => Term a -> Term a -> Term a
absNumTerm :: (SupportedPrim a, Num a) => Term a -> Term a
signumNumTerm :: (SupportedPrim a, Num a) => Term a -> Term a
ltNumTerm :: (SupportedPrim a, Num a, Ord a) => Term a -> Term a -> Term Bool
leNumTerm :: (SupportedPrim a, Num a, Ord a) => Term a -> Term a -> Term Bool