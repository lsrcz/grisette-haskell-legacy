module Grisette.Data.Prim.Model
  ( Model (..),
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

import Control.Monad.Memo
import Data.Dynamic
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Typeable
import Grisette.Data.MemoUtils
import Grisette.Data.Prim.InternedTerm
import Unsafe.Coerce

newtype Model = Model (M.HashMap Symbol Dynamic) deriving (Show)

empty :: Model
empty = Model M.empty

valueOf :: forall t. (Typeable t) => Model -> Symbol -> Maybe t
valueOf (Model m) sym =
  (\d -> fromDyn @t d (error $ "Bad type" ++ show (typeRep (Proxy @t)) ++ "for symbol " ++ show sym))
    <$> M.lookup sym m

exceptFor :: Model -> S.HashSet TermSymbol -> Model
exceptFor (Model m) s =
  Model $ S.foldl' (\acc (TermSymbol _ sym) -> M.delete sym acc) m s

restrictTo :: Model -> S.HashSet TermSymbol -> Model
restrictTo (Model m) s =
  Model $
    S.foldl'
      ( \acc (TermSymbol _ sym) -> case M.lookup sym m of
          Just v -> M.insert sym v acc
          Nothing -> acc
      )
      M.empty
      s

extendTo :: Model -> S.HashSet TermSymbol -> Model
extendTo (Model m) s =
  Model $
    S.foldl'
      ( \acc (TermSymbol (_ :: Proxy t) sym) -> case M.lookup sym acc of
          Just _ -> acc
          Nothing -> M.insert sym (defaultValueDynamic @t) acc
      )
      m
      s

exact :: Model -> S.HashSet TermSymbol -> Model
exact m s = restrictTo (extendTo m s) s

insert :: (Typeable a) => Model -> TermSymbol -> a -> Model
insert (Model m) (TermSymbol p sym) v =
  if typeRep p == typeOf v
    then Model $ M.insert sym (toDyn v) m
    else error "Bad value type"

evaluateSomeTermMemo :: Bool -> Model -> SomeTerm -> MemoState (MemoHashMap SomeTerm SomeTerm) SomeTerm SomeTerm SomeTerm
evaluateSomeTermMemo fillDefault (Model ma) = go
  where
    go :: SomeTerm -> MemoState (MemoHashMap SomeTerm SomeTerm) SomeTerm SomeTerm SomeTerm
    go c@(SomeTerm ConcTerm {}) = return c
    go c@(SomeTerm ((SymbTerm _ (TermSymbol (_ :: Proxy t) sym)) :: Term a)) = return $ case M.lookup sym ma of
      Nothing -> if fillDefault then SomeTerm $ concTerm (defaultValue @t) else c
      Just dy -> SomeTerm $ concTerm (fromDyn @a dy undefined)
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

evaluateTerm :: forall a. (SupportedPrim a) => Bool -> Model -> Term a -> Term a
evaluateTerm fillDefault m t = case evaluateSomeTerm fillDefault m $ SomeTerm t of
  SomeTerm (t1 :: Term b) -> unsafeCoerce @(Term b) @(Term a) t1
