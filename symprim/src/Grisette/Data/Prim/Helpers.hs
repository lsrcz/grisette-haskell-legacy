{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.Helpers
  ( pattern UnaryTermPatt,
    pattern BinaryTermPatt,
    pattern TernaryTermPatt,
    PartialFunc,
    PartialRuleUnary,
    TotalRuleUnary,
    PartialRuleBinary,
    TotalRuleBinary,
    totalize,
    totalize2,
    UnaryPartialStrategy (..),
    unaryPartial,
    BinaryCommPartialStrategy (..),
    BinaryPartialStrategy (..),
    binaryPartial,
  )
where

import Data.Typeable
import Grisette.Data.Prim.InternedTerm

unaryTermView :: forall a b tag. (Typeable tag, Typeable b) => Term a -> Maybe (tag, Term b)
unaryTermView (UnaryTerm _ (tag :: tagt) t1) =
  (,) <$> cast tag <*> castTerm t1
unaryTermView _ = Nothing

pattern UnaryTermPatt :: forall a b tag. (Typeable tag, Typeable b) => tag -> Term b -> Term a
pattern UnaryTermPatt tag t <- (unaryTermView @a @b @tag -> Just (tag, t))

binaryTermView :: forall a b c tag. (Typeable tag, Typeable b, Typeable c) => Term a -> Maybe (tag, Term b, Term c)
binaryTermView (BinaryTerm _ (tag :: tagt) t1 t2) =
  (,,) <$> cast tag <*> castTerm t1 <*> castTerm t2
binaryTermView _ = Nothing

pattern BinaryTermPatt :: forall a b c tag. (Typeable tag, Typeable b, Typeable c) => tag -> Term b -> Term c -> Term a
pattern BinaryTermPatt tag l r <- (binaryTermView @a @b @c @tag -> Just (tag, l, r))

ternaryTermView ::
  forall a b c d tag.
  (Typeable tag, Typeable b, Typeable c, Typeable d) =>
  Term a ->
  Maybe (tag, Term b, Term c, Term d)
ternaryTermView (TernaryTerm _ (tag :: tagt) t1 t2 t3) =
  (,,,) <$> cast tag <*> castTerm t1 <*> castTerm t2 <*> castTerm t3
ternaryTermView _ = Nothing

pattern TernaryTermPatt ::
  forall a b c d tag.
  (Typeable tag, Typeable b, Typeable c, Typeable d) =>
  tag ->
  Term b ->
  Term c ->
  Term d ->
  Term a
pattern TernaryTermPatt tag a b c <- (ternaryTermView @a @b @c @d @tag -> Just (tag, a, b, c))

type PartialFunc a b = a -> Maybe b

type PartialRuleUnary a b = PartialFunc (Term a) (Term b)

type TotalRuleUnary a b = Term a -> Term b

type PartialRuleBinary a b c = Term a -> PartialFunc (Term b) (Term c)

type TotalRuleBinary a b c = Term a -> Term b -> Term c

totalize :: PartialFunc a b -> (a -> b) -> a -> b
totalize partial fallback a =
  case partial a of
    Just b -> b
    Nothing -> fallback a

totalize2 :: (a -> PartialFunc b c) -> (a -> b -> c) -> a -> b -> c
totalize2 partial fallback a b =
  case partial a b of
    Just c -> c
    Nothing -> fallback a b

class UnaryPartialStrategy tag a b | tag a -> b where
  extractor :: Term a -> Maybe a
  constantHandler :: a -> Maybe (Term b)
  nonConstantHandler :: Term a -> Maybe (Term b)

unaryPartial :: forall tag a b. (UnaryPartialStrategy tag a b) => PartialRuleUnary a b
unaryPartial a = case extractor @tag @a @b a of
  Nothing -> nonConstantHandler @tag @a @b a
  Just a' -> constantHandler @tag @a @b a'

class BinaryCommPartialStrategy tag a c | tag a -> c where
  singleConstantHandler :: a -> Term a -> Maybe (Term c)

class BinaryPartialStrategy tag a b c | tag a b -> c where
  extractora :: Term a -> Maybe a
  extractorb :: Term b -> Maybe b
  allConstantHandler :: a -> b -> Maybe (Term c)
  leftConstantHandler :: a -> Term b -> Maybe (Term c)
  default leftConstantHandler :: (a ~ b, BinaryCommPartialStrategy tag a c) => a -> Term b -> Maybe (Term c)
  leftConstantHandler = singleConstantHandler @tag @a
  rightConstantHandler :: Term a -> b -> Maybe (Term c)
  default rightConstantHandler :: (a ~ b, BinaryCommPartialStrategy tag a c) => Term a -> b -> Maybe (Term c)
  rightConstantHandler = flip $ singleConstantHandler @tag @a
  nonBinaryConstantHandler :: Term a -> Term b -> Maybe (Term c)

binaryPartial :: forall tag a b c. (BinaryPartialStrategy tag a b c) => PartialRuleBinary a b c
binaryPartial a b = case (extractora @tag @a @b @c a, extractorb @tag @a @b @c b) of
  (Nothing, Nothing) -> nonBinaryConstantHandler @tag @a @b @c a b
  (Just a', Nothing) -> leftConstantHandler @tag @a @b @c a' b
  (Nothing, Just b') -> rightConstantHandler @tag @a @b @c a b'
  (Just a', Just b') -> allConstantHandler @tag @a @b @c a' b'
