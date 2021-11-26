{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Data.Prim.Model where

import Data.Dynamic
import Data.HashMap.Lazy as M
import Data.HashSet as S
import Data.Typeable
import Grisette.Data.Prim.InternedTerm

newtype Model = Model (M.HashMap Symbol Dynamic)

empty :: Model
empty = Model M.empty

valueOf :: forall t. (Typeable t) => Model -> Symbol -> Maybe t
valueOf (Model m) sym =
  (\d -> fromDyn @t d (error $ "Bad type" ++ show (typeRep (Proxy @t)) ++ "for symbol " ++ show sym))
    <$> M.lookup sym m

exceptFor :: Model -> S.HashSet TermSymbol -> Model
exceptFor (Model m) s =
  Model $ S.foldl' (\acc (TermSymbol sym _) -> M.delete sym acc) m s

restrictTo :: Model -> S.HashSet TermSymbol -> Model
restrictTo (Model m) s =
  Model $ S.foldl' (\acc (TermSymbol sym _) -> case M.lookup sym m of
    Just v -> M.insert sym v acc
    Nothing -> acc) M.empty s

extendTo :: Model -> S.HashSet TermSymbol -> Model
extendTo (Model m) s = Model $
  S.foldl' (\acc (TermSymbol sym dv) -> case M.lookup sym acc of
    Just _ -> acc
    Nothing -> M.insert sym dv acc) m s

exact :: Model -> S.HashSet TermSymbol -> Model
exact m s = restrictTo (extendTo m s) s

insert :: (Typeable a) => Model -> TermSymbol -> a -> Model
insert (Model m) (TermSymbol sym df) v =
  if dynTypeRep df == typeOf v
    then Model $ M.insert sym (toDyn v) m
    else error "Bad value type"

evaluateTerm :: forall a. (Typeable a, Show a) => Bool -> Model -> Term a -> Term a
evaluateTerm _ _ c@(ConcTerm _ _) = c
evaluateTerm fillDefault (Model m) c@(SymbTerm _ (TermSymbol sym df)) = case M.lookup sym m of
  Nothing -> if fillDefault then concTerm (fromDyn df undefined) else c
  Just dy -> concTerm (fromDyn dy undefined)
evaluateTerm fillDefault m (UnaryTerm _ tag arg) = partialEvalUnary tag (evaluateTerm fillDefault m arg)
evaluateTerm fillDefault m (BinaryTerm _ tag arg1 arg2) =
  partialEvalBinary tag (evaluateTerm fillDefault m arg1) (evaluateTerm fillDefault m arg2)
evaluateTerm fillDefault m (TernaryTerm _ tag arg1 arg2 arg3) =
  partialEvalTernary
    tag
    (evaluateTerm fillDefault m arg1)
    (evaluateTerm fillDefault m arg2)
    (evaluateTerm fillDefault m arg3)
