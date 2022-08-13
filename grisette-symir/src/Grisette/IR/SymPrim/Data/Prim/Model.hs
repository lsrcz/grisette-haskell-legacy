{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

module Grisette.IR.SymPrim.Data.Prim.Model
  ( Model (..),
    equation,
    empty,
    valueOf,
    exceptFor,
    restrictTo,
    extendTo,
    exact,
    insert,
    evaluateTerm,
  )
where

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Hashable
import Data.Typeable
import GHC.Generics
import Grisette.Core.Data.MemoUtils
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.ModelValue
import Unsafe.Coerce
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors

newtype Model = Model (M.HashMap TermSymbol ModelValue) deriving (Show, Eq, Generic, Hashable)

equation :: Model -> TermSymbol -> Maybe (Term Bool)
equation m tsym@(TermSymbol (_ :: Proxy a) sym) =
  case valueOf m tsym of
    Just (v :: a) -> Just $ eqterm (symbTerm sym) (concTerm v)
    Nothing -> Nothing

empty :: Model
empty = Model M.empty

valueOf :: forall t. (Typeable t) => Model -> TermSymbol -> Maybe t
valueOf (Model m) sym =
  (unsafeFromModelValue @t)
    <$> M.lookup sym m

exceptFor :: Model -> S.HashSet TermSymbol -> Model
exceptFor (Model m) s =
  Model $ S.foldl' (flip M.delete) m s

restrictTo :: Model -> S.HashSet TermSymbol -> Model
restrictTo (Model m) s =
  Model $
    S.foldl'
      ( \acc sym -> case M.lookup sym m of
          Just v -> M.insert sym v acc
          Nothing -> acc
      )
      M.empty
      s

extendTo :: Model -> S.HashSet TermSymbol -> Model
extendTo (Model m) s =
  Model $
    S.foldl'
      ( \acc sym@(TermSymbol (_ :: Proxy t) _) -> case M.lookup sym acc of
          Just _ -> acc
          Nothing -> M.insert sym (defaultValueDynamic (Proxy @t)) acc
      )
      m
      s

exact :: Model -> S.HashSet TermSymbol -> Model
exact m s = restrictTo (extendTo m s) s

insert :: (Eq a, Show a, Hashable a, Typeable a) => Model -> TermSymbol -> a -> Model
insert (Model m) sym@(TermSymbol p _) v =
  if typeRep p == typeOf v
    then Model $ M.insert sym (toModelValue v) m
    else error "Bad value type"

evaluateSomeTerm :: Bool -> Model -> SomeTerm -> SomeTerm
evaluateSomeTerm fillDefault (Model ma) = gomemo
  where
    gomemo = htmemo go
    gotyped :: (SupportedPrim a) => Term a -> Term a
    gotyped a = case gomemo (SomeTerm a) of
      SomeTerm v -> unsafeCoerce v
    go c@(SomeTerm ConcTerm {}) = c
    go c@(SomeTerm ((SymbTerm _ sym@(TermSymbol (_ :: Proxy t) _)) :: Term a)) = case M.lookup sym ma of
      Nothing -> if fillDefault then SomeTerm $ concTerm (defaultValue @t) else c
      Just dy -> SomeTerm $ concTerm (unsafeFromModelValue @a dy)
    go (SomeTerm (UnaryTerm _ tag (arg :: Term a))) = goUnary (partialEvalUnary tag) arg
    go (SomeTerm (BinaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2))) =
      goBinary (partialEvalBinary tag) arg1 arg2
    go (SomeTerm (TernaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2) (arg3 :: Term a3))) = do
          SomeTerm $
            partialEvalTernary
              tag
              (gotyped arg1)
              (gotyped arg2)
              (gotyped arg3)
    go (SomeTerm (NotTerm _ arg)) = goUnary notb arg
    go (SomeTerm (OrTerm _ arg1 arg2)) =
      goBinary orb arg1 arg2
    go (SomeTerm (AndTerm _ arg1 arg2)) =
      goBinary andb arg1 arg2
    goUnary :: (SupportedPrim a, SupportedPrim b) => (Term a -> Term b) -> Term a -> SomeTerm
    goUnary f a = SomeTerm $ f (gotyped a)
    goBinary :: (SupportedPrim a, SupportedPrim b, SupportedPrim c) =>
      (Term a -> Term b -> Term c) -> Term a -> Term b -> SomeTerm
    goBinary f a b = SomeTerm $ f (gotyped a) (gotyped b)

evaluateTerm :: forall a. (SupportedPrim a) => Bool -> Model -> Term a -> Term a
evaluateTerm fillDefault m t = case evaluateSomeTerm fillDefault m $ SomeTerm t of
  SomeTerm (t1 :: Term b) -> unsafeCoerce @(Term b) @(Term a) t1
