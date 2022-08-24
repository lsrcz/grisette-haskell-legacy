{-# LANGUAGE TemplateHaskell #-}

module Interpreter where

import Control.Monad.Except
import Control.Monad.State
import GHC.Generics
import Grisette

data Expr
  = Lit LitExpr
  | Ops OpsExpr
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default Expr)

data LitExpr
  = BoolLit SymBool
  | ListLit (UnionM [SymBool])
  | UnitLit
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default LitExpr)

data OpsExpr
  = HeadExpr (UnionM Expr)
  | TailExpr (UnionM Expr)
  | ConsExpr (UnionM Expr) (UnionM Expr)
  | AndExpr (UnionM Expr) (UnionM Expr)
  | NotExpr (UnionM Expr)
  | VarExpr SymInteger
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default OpsExpr)

$(makeUnionMWrapper "u" ''OpsExpr)
$(makeUnionMWrapper "u" ''LitExpr)
$(makeUnionMWrapper "u" ''Expr)

data ExprSpec = ExprSpec
  { exprDepth :: Integer,
    exprListLength :: Integer
  }
  deriving (Show)

instance GenSym (Sym Bool) Integer LitExpr where
  genSymFresh listLength = do
    b <- genSymSimpleFresh ()
    l <- genSymFresh listLength
    choose [BoolLit b, ListLit l, UnitLit]

instance GenSym (Sym Bool) ExprSpec OpsExpr where
  genSymFresh (ExprSpec d l) = do
    l1 <- genSymFresh (ExprSpec (d - 1) l)
    l2 <- genSymFresh (ExprSpec (d - 1) l)
    v <- genSymSimpleFresh ()
    choose
      [ HeadExpr l1,
        TailExpr l1,
        ConsExpr l1 l2,
        AndExpr l1 l2,
        NotExpr l1,
        VarExpr v
      ]

instance GenSym (Sym Bool) ExprSpec Expr where
  genSymFresh e@(ExprSpec d l) =
    if d <= 0
      then do
        lit <- genSymFresh l
        return $ mrgFmap Lit lit
      else do
        lit <- genSymFresh l
        ops <- genSymFresh e
        chooseU [Lit <$> lit, Ops <$> ops]

data Stmt
  = DefineStmt SymInteger (UnionM Expr)
  | ValueStmt (UnionM Expr)
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default Stmt)

instance GenSym (Sym Bool) ExprSpec Stmt where
  genSymFresh e = do
    expr <- genSymFresh e
    vari <- genSymSimpleFresh ()
    choose [DefineStmt vari expr, ValueStmt expr]

data Error
  = Typer TyperError
  | Runtime RuntimeError
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default Error)

data TyperError
  = TypeVarNotFound
  | TypeMismatch
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default TyperError)

data RuntimeError
  = RuntimeVarNotFound
  | RuntimeTypeMismatch
  | RuntimeRuntimeError
  deriving (Generic, Show)
  deriving (Evaluate Model, Mergeable SymBool) via (Default RuntimeError)

data Type
  = UnitType
  | BoolType
  | ListType
  deriving (Generic, Show, Eq)
  deriving (Evaluate Model, Mergeable SymBool) via (Default Type)

$(makeUnionMWrapper "u" ''Type)

type TypingEnv = [(SymInteger, UnionM Type)]

typeCheck :: TypingEnv -> Expr -> ExceptT Error UnionM Type
typeCheck _ (Lit UnitLit) = uUnitType
typeCheck _ (Lit (BoolLit _)) = uBoolType
typeCheck _ (Lit (ListLit _)) = uListType
typeCheck env (Ops (HeadExpr e)) = do
  et <- typeCheck env #~ e
  if et == ListType then uBoolType else throwError $ Typer TypeMismatch
typeCheck env (Ops (TailExpr e)) = do
  et <- typeCheck env #~ e
  if et == ListType then uListType else throwError $ Typer TypeMismatch
typeCheck env (Ops (ConsExpr h t)) = do
  th <- typeCheck env #~ h
  tt <- typeCheck env #~ t
  if th == BoolType && tt == ListType then uListType else throwError $ Typer TypeMismatch
typeCheck env (Ops (AndExpr l r)) = do
  tl <- typeCheck env #~ l
  tr <- typeCheck env #~ r
  if tl == BoolType && tr == BoolType then uBoolType else throwError $ Typer TypeMismatch
typeCheck env (Ops (NotExpr e)) = do
  et <- typeCheck env #~ e
  if et == BoolType then uBoolType else throwError $ Typer TypeMismatch
typeCheck env (Ops (VarExpr i)) = resolveEnv env i
  where
    resolveEnv [] _ = throwError $ Typer TypeVarNotFound
    resolveEnv ((hdi, hdt) : tl) i1 = mrgIf (hdi ==~ i1) (lift hdt) $ resolveEnv tl i1

typeCheckStmt :: Stmt -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmt (DefineStmt i expr) = StateT $ \st -> mrgFmap (\t -> (UnitType, (i, mrgReturn t) : st)) $ typeCheck st #~ expr
typeCheckStmt (ValueStmt expr) = StateT $ \st -> mrgFmap (,st) $ mrgLift expr >>= typeCheck st

typeCheckStmtListU :: [UnionM Stmt] -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmtListU [] = mrgReturn UnitType
typeCheckStmtListU [x] = typeCheckStmt #~ x
typeCheckStmtListU (x : xs) = typeCheckStmt #~ x >>~ typeCheckStmtListU xs

reduceHead :: LitExpr -> ExceptT Error UnionM LitExpr
reduceHead (ListLit l) = do
  l1 <- mrgLift l
  case l1 of
    [] -> throwError $ Runtime RuntimeRuntimeError
    sb : _ -> uBoolLit sb
reduceHead _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceTail :: LitExpr -> ExceptT Error UnionM LitExpr
reduceTail (ListLit l) = do
  l1 <- mrgLift l
  case l1 of
    [] -> throwError $ Runtime RuntimeRuntimeError
    _ : t -> uListLit $ mrgReturn t
reduceTail _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceCons :: LitExpr -> LitExpr -> ExceptT Error UnionM LitExpr
reduceCons (BoolLit b) (ListLit t) = do
  t1 <- lift t
  uListLit $ mrgReturn $ b : t1
reduceCons _ _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceNot :: LitExpr -> ExceptT Error UnionM LitExpr
reduceNot (BoolLit b) = uBoolLit $ nots b
reduceNot _ = throwError $ Runtime RuntimeTypeMismatch

reduceAnd :: LitExpr -> LitExpr -> ExceptT Error UnionM LitExpr
reduceAnd (BoolLit l) (BoolLit r) = uBoolLit $ l &&~ r
reduceAnd _ _ = throwError $ Runtime RuntimeTypeMismatch

type ExecutingEnv = [(SymInteger, UnionM LitExpr)]

reduceValue :: ExecutingEnv -> SymInteger -> ExceptT Error UnionM LitExpr
reduceValue [] _ = throwError $ Runtime RuntimeVarNotFound
reduceValue ((hdi, hdv) : tl) h = mrgIf (hdi ==~ h) (lift hdv) $ reduceValue tl h

interpret :: ExecutingEnv -> Expr -> ExceptT Error UnionM LitExpr
interpret env (Ops (HeadExpr e)) = do
  ev <- interpret env #~ e
  reduceHead ev
interpret env (Ops (TailExpr e)) = do
  ev <- interpret env #~ e
  reduceTail ev
interpret env (Ops (ConsExpr h t)) = do
  hv <- interpret env #~ h
  tv <- interpret env #~ t
  reduceCons hv tv
interpret env (Ops (AndExpr l r)) = do
  lv <- interpret env #~ l
  rv <- interpret env #~ r
  reduceAnd lv rv
interpret env (Ops (NotExpr e)) = do
  ev <- interpret env #~ e
  reduceNot ev
interpret env (Ops (VarExpr i)) = reduceValue env i
interpret _ (Lit l) = mrgReturn l

interpretStmt :: Stmt -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmt (DefineStmt i expr) = StateT $ \st -> mrgFmap (\t -> (UnitLit, (i, mrgReturn t) : st)) $ interpret st #~ expr
interpretStmt (ValueStmt expr) = StateT $ \env -> mrgFmap (,env) $ mrgLift expr >>= interpret env

interpretStmtList :: [Stmt] -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmtList [] = mrgReturn UnitLit
interpretStmtList [x] = interpretStmt x
interpretStmtList (x : xs) = interpretStmt x >>~ interpretStmtList xs

interpretStmtListU :: [UnionM Stmt] -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmtListU [] = mrgReturn UnitLit
interpretStmtListU [x] = interpretStmt #~ x
interpretStmtListU (x : xs) = interpretStmt #~ x >>~ interpretStmtListU xs

checkAndInterpretStmtUListU :: UnionM [UnionM Stmt] -> ExceptT Error UnionM LitExpr
checkAndInterpretStmtUListU st = evalStateT (typeCheckStmtListU #~ st) [] >>~ evalStateT (interpretStmtListU #~ st) []
