{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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
  Model $ S.foldl' (\acc sym -> M.delete sym acc) m s

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

{-
evaluateSomeTermMemo :: Bool -> Model -> SomeTerm -> MemoState (MemoHashMap SomeTerm SomeTerm) SomeTerm SomeTerm SomeTerm
evaluateSomeTermMemo fillDefault (Model ma) = go
  where
    go :: SomeTerm -> MemoState (MemoHashMap SomeTerm SomeTerm) SomeTerm SomeTerm SomeTerm
    go c@(SomeTerm ConcTerm {}) = return c
    go c@(SomeTerm ((SymbTerm _ sym@(TermSymbol (_ :: Proxy t) _)) :: Term a)) = return $ case M.lookup sym ma of
      Nothing -> if fillDefault then SomeTerm $ concTerm (defaultValue @t) else c
      Just dy -> SomeTerm $ concTerm (unsafeFromModelValue @a dy)
    go (SomeTerm (UnaryTerm _ tag (arg :: Term a))) = do
      SomeTerm argv <- memo go (SomeTerm arg)
      return $ SomeTerm $ partialEvalUnary tag (unsafeCoerce argv :: Term a)
    go (SomeTerm (BinaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2))) = do
      SomeTerm arg1v <- memo go (SomeTerm arg1)
      SomeTerm arg2v <- memo go (SomeTerm arg2)
      return $
        SomeTerm $
          partialEvalBinary
            tag
            (unsafeCoerce arg1v :: Term a1)
            (unsafeCoerce arg2v :: Term a2)
    go (SomeTerm (TernaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2) (arg3 :: Term a3))) = do
      SomeTerm arg1v <- memo go (SomeTerm arg1)
      SomeTerm arg2v <- memo go (SomeTerm arg2)
      SomeTerm arg3v <- memo go (SomeTerm arg3)
      return $
        SomeTerm $
          partialEvalTernary
            tag
            (unsafeCoerce arg1v :: Term a1)
            (unsafeCoerce arg2v :: Term a2)
            (unsafeCoerce arg3v :: Term a3)

evaluateSomeTerm :: Bool -> Model -> SomeTerm -> SomeTerm
evaluateSomeTerm fillDefault m t1 = evalMemoState (evaluateSomeTermMemo fillDefault m t1) (MemoHashMap M.empty)
-}

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
    go (SomeTerm (UnaryTerm _ tag (arg :: Term a))) = do
      SomeTerm $ partialEvalUnary tag (gotyped arg)
    go (SomeTerm (BinaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2))) =
          SomeTerm $
            partialEvalBinary
              tag
              (gotyped arg1)
              (gotyped arg2)
    go (SomeTerm (TernaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2) (arg3 :: Term a3))) = do
          SomeTerm $
            partialEvalTernary
              tag
              (gotyped arg1)
              (gotyped arg2)
              (gotyped arg3)

evaluateTerm :: forall a. (SupportedPrim a) => Bool -> Model -> Term a -> Term a
evaluateTerm fillDefault m t = case evaluateSomeTerm fillDefault m $ SomeTerm t of
  SomeTerm (t1 :: Term b) -> unsafeCoerce @(Term b) @(Term a) t1
