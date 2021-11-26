{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Data.Prim.Model where

import Data.Dynamic
import Data.HashMap.Lazy as M
import Data.HashSet as S
import Data.Typeable
import Grisette.Data.Prim.InternedTerm
import Data.Maybe
import Control.Monad.State
import Unsafe.Coerce

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

evaluateSomeTerm :: Bool -> Model -> SomeTerm -> SomeTerm
evaluateSomeTerm fillDefault (Model ma) t1 = evalState (gocached t1) M.empty
  where
    gocached :: SomeTerm -> State (M.HashMap SomeTerm SomeTerm) SomeTerm
    gocached t = do
      v <- gets (M.lookup t)
      case v of
        Just x -> return x
        Nothing -> do
          res <- go t
          st <- get
          put $ M.insert t res st
          return res
    go :: SomeTerm -> State (M.HashMap SomeTerm SomeTerm) SomeTerm
    go c@(SomeTerm ConcTerm{}) = return c
    go c@(SomeTerm ((SymbTerm _ (TermSymbol sym df)) :: Term a)) = return $ case M.lookup sym ma of
      Nothing -> if fillDefault then SomeTerm $ concTerm $ fromDyn @a df undefined else c
      Just dy -> SomeTerm $ concTerm (fromDyn @a dy undefined)
    go (SomeTerm (UnaryTerm _ tag (arg :: Term a))) = do
      SomeTerm argv <- gocached (SomeTerm arg)
      return $ SomeTerm $ partialEvalUnary tag (unsafeCoerce argv :: Term a)
    go (SomeTerm (BinaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2))) = do
      SomeTerm arg1v <- gocached (SomeTerm arg1)
      SomeTerm arg2v <- gocached (SomeTerm arg2)
      return $ SomeTerm $ partialEvalBinary tag
        (unsafeCoerce arg1v :: Term a1)
        (unsafeCoerce arg2v :: Term a2)
    go (SomeTerm (TernaryTerm _ tag (arg1 :: Term a1) (arg2 :: Term a2) (arg3 :: Term a3))) =do
      SomeTerm arg1v <- gocached (SomeTerm arg1)
      SomeTerm arg2v <- gocached (SomeTerm arg2)
      SomeTerm arg3v <- gocached (SomeTerm arg3)
      return $ SomeTerm $ partialEvalTernary tag
        (unsafeCoerce arg1v :: Term a1)
        (unsafeCoerce arg2v :: Term a2)
        (unsafeCoerce arg3v :: Term a3)

evaluateTerm :: forall a. (SupportedPrim a) => Bool -> Model -> Term a -> Term a
evaluateTerm fillDefault m t = case evaluateSomeTerm fillDefault m $ SomeTerm t of
  SomeTerm (t1 :: Term b) -> fromJust $ cast @(Term b) @(Term a) t1
