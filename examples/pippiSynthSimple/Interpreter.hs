{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module PippiInterpreter where

import Control.Monad.Except
import Control.Monad.State
import GHC.Generics
import Grisette.Control.Monad
import Grisette.Control.Monad.Trans
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.SymGen
import Grisette.Data.Functor
import Grisette.Data.Prim.Model
import Grisette.Data.SymPrim
import Grisette.Data.Class.ToSym

data Expr
  = Lit LitExpr
  | Ops OpsExpr
  deriving (Generic, Show)

data LitExpr
  = BoolLit SymBool
  | ListLit (UnionM [SymBool])
  | UnitLit
  deriving (Generic, Show)

data OpsExpr
  = HeadExpr (UnionM Expr)
  | TailExpr (UnionM Expr)
  | ConsExpr (UnionM Expr) (UnionM Expr)
  | AndExpr (UnionM Expr) (UnionM Expr)
  | NotExpr (UnionM Expr)
  | VarExpr SymInteger
  deriving (Generic, Show)

-- COORDINATE STUFF
data Coord = [Int, Int]

data MovementExpr 
   = Coord coord
   | Movement movement coord
   deriving (Generic, Show)

data Movement 
   = MoveUp    (UnionM MovementExpr)
   = MoveDown  (UnionM MovementExpr)
   = MoveLeft  (UnionM MovementExpr)
   = MoveRight (UnionM MovementExpr)

omg


data ExprSpec = ExprSpec
  { exprDepth :: Integer,
    exprListLength :: Integer
  }
  deriving (Show)

instance SymGen (Sym Bool) Integer LitExpr where
  genSymIndexed listLength = do
    b <- genSymSimpleIndexed @SymBool ()
    l <- genSymIndexed @SymBool listLength
    choose (BoolLit b) [ListLit l, UnitLit]

instance SymGen (Sym Bool) ExprSpec OpsExpr where
  genSymIndexed (ExprSpec d l) = do
    l1 <- genSymIndexed @SymBool (ExprSpec (d - 1) l)
    l2 <- genSymIndexed @SymBool (ExprSpec (d - 1) l)
    v <- genSymSimpleIndexed @SymBool ()
    choose
      (HeadExpr l1)
      [ TailExpr l1,
        ConsExpr l1 l2,
        AndExpr l1 l2,
        NotExpr l1,
        VarExpr v
      ]

instance SymGen (Sym Bool) ExprSpec Expr where
  genSymIndexed e@(ExprSpec d l) =
    merge
      <$> if d <= 0
        then do
          lit <- genSymIndexed @SymBool l
          return $ Lit <$> lit
        else do
          lit <- genSymIndexed @SymBool l
          ops <- genSymIndexed @SymBool e
          chooseU (Lit <$> lit) [Ops <$> ops]

data Stmt
  = DefineStmt SymInteger (UnionM Expr)
  | ValueStmt (UnionM Expr)
  deriving (Generic, Show)

instance SymGen (Sym Bool) ExprSpec Stmt where
  genSymIndexed e = do
    expr <- genSymIndexed @SymBool e
    vari <- genSymSimpleIndexed @SymBool ()
    choose (DefineStmt vari expr) [ValueStmt expr]

instance Mergeable (Sym Bool) Expr

instance Mergeable (Sym Bool) LitExpr

instance Mergeable (Sym Bool) OpsExpr

instance Mergeable (Sym Bool) Stmt

instance SymEval Model LitExpr

instance SymEval Model OpsExpr

instance SymEval Model Expr

instance SymEval Model Stmt

instance ToSym LitExpr LitExpr
instance ToSym OpsExpr OpsExpr
instance ToSym Expr Expr
instance ToSym Stmt Stmt

data Error
  = Typer TyperError
  | Runtime RuntimeError
  deriving (Generic, Show)

data TyperError
  = TypeVarNotFound
  | TypeMismatch
  deriving (Generic, Show)

data RuntimeError
  = RuntimeVarNotFound
  | RuntimeTypeMismatch
  | RuntimeRuntimeError
  deriving (Generic, Show)

instance Mergeable (Sym Bool) Error

instance Mergeable (Sym Bool) TyperError

instance Mergeable (Sym Bool) RuntimeError

instance SymEval Model Error

instance SymEval Model TyperError

instance SymEval Model RuntimeError

data Type
  = UnitType
  | BoolType
  | ListType
  deriving (Generic, Show, Eq)

instance Mergeable (Sym Bool) Type

type TypingEnv = [(SymInteger, UnionM Type)]

typeCheckU :: TypingEnv -> UnionM Expr -> ExceptT Error UnionM Type
typeCheckU env u = lift u >>= typeCheck env

typeCheck :: TypingEnv -> Expr -> ExceptT Error UnionM Type
typeCheck _ (Lit UnitLit) = mrgReturn UnitType
typeCheck _ (Lit (BoolLit _)) = mrgReturn BoolType
typeCheck _ (Lit (ListLit _)) = mrgReturn ListType
typeCheck env (Ops (HeadExpr e)) = do
  et <- typeCheckU env e
  merge $ if et == ListType then return BoolType else throwError $ Typer TypeMismatch
typeCheck env (Ops (TailExpr e)) = do
  et <- typeCheckU env e
  merge $ if et == ListType then return ListType else throwError $ Typer TypeMismatch
typeCheck env (Ops (ConsExpr h t)) = do
  th <- typeCheckU env h
  tt <- typeCheckU env t
  merge $ if th == BoolType && tt == ListType then return ListType else throwError $ Typer TypeMismatch
typeCheck env (Ops (AndExpr l r)) = do
  tl <- typeCheckU env l
  tr <- typeCheckU env r
  merge $ if tl == BoolType && tr == BoolType then return BoolType else throwError $ Typer TypeMismatch
typeCheck env (Ops (NotExpr e)) = do
  et <- typeCheckU env e
  merge $ if et == BoolType then return BoolType else throwError $ Typer TypeMismatch
typeCheck env (Ops (VarExpr i)) = resolveEnv env i
  where
    resolveEnv [] _ = merge $ throwError $ Typer TypeVarNotFound
    resolveEnv ((hdi, hdt) : tl) i1 = mrgIf @SymBool (hdi ==~ i1) (lift hdt) $ resolveEnv tl i1

typeCheckStmt :: Stmt -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmt (DefineStmt i expr) = StateT $ \st -> mrgFmap (\t -> (UnitType, (i, mrgSingle t) : st)) $ typeCheckU st expr
typeCheckStmt (ValueStmt expr) = StateT $ \st -> mrgFmap (,st) $ mrgLift expr >>= typeCheck st

typeCheckStmtU :: UnionM Stmt -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmtU stmt = (lift . lift) stmt >>= typeCheckStmt

typeCheckStmtList :: [Stmt] -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmtList [] = mrgReturn UnitType
typeCheckStmtList [x] = typeCheckStmt x
typeCheckStmtList (x : xs) = typeCheckStmt x >>~ typeCheckStmtList xs

typeCheckStmtListU :: [UnionM Stmt] -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmtListU [] = mrgReturn UnitType
typeCheckStmtListU [x] = typeCheckStmtU x
typeCheckStmtListU (x : xs) = typeCheckStmtU x >>~ typeCheckStmtListU xs

typeCheckStmtUListU :: UnionM [UnionM Stmt] -> StateT TypingEnv (ExceptT Error UnionM) Type
typeCheckStmtUListU u = (lift . lift) u >>= typeCheckStmtListU

reduceHead :: LitExpr -> ExceptT Error UnionM LitExpr
reduceHead (ListLit l) = do
  l1 <- mrgLift l
  merge $ case l1 of
    [] -> throwError $ Runtime RuntimeRuntimeError
    sb : _ -> mrgReturn $ BoolLit sb
reduceHead _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceTail :: LitExpr -> ExceptT Error UnionM LitExpr
reduceTail (ListLit l) = do
  l1 <- mrgLift l
  merge $ case l1 of
    [] -> throwError $ Runtime RuntimeRuntimeError
    _ : t -> mrgReturn $ ListLit $ mrgSingle t
reduceTail _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceCons :: LitExpr -> LitExpr -> ExceptT Error UnionM LitExpr
reduceCons (BoolLit b) (ListLit t) = do
  t1 <- lift t
  mrgReturn $ ListLit $ mrgSingle $ b : t1
reduceCons _ _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceNot :: LitExpr -> ExceptT Error UnionM LitExpr
reduceNot (BoolLit b) = mrgReturn $ BoolLit $ nots b
reduceNot _ = merge $ throwError $ Runtime RuntimeTypeMismatch

reduceAnd :: LitExpr -> LitExpr -> ExceptT Error UnionM LitExpr
reduceAnd (BoolLit l) (BoolLit r) = mrgReturn $ BoolLit $ l &&~ r
reduceAnd _ _ = merge $ throwError $ Runtime RuntimeTypeMismatch

type ExecutingEnv = [(SymInteger, UnionM LitExpr)]

reduceValue :: ExecutingEnv -> SymInteger -> ExceptT Error UnionM LitExpr
reduceValue [] _ = merge $ throwError $ Runtime RuntimeVarNotFound
reduceValue ((hdi, hdv) : tl) h = mrgIf @SymBool (hdi ==~ h) (lift hdv) $ reduceValue tl h

interpretU :: ExecutingEnv -> UnionM Expr -> ExceptT Error UnionM LitExpr
interpretU env u = mrgLift u >>= interpret env

interpret :: ExecutingEnv -> Expr -> ExceptT Error UnionM LitExpr
interpret env (Ops (HeadExpr e)) = do
  ev <- interpretU env e
  reduceHead ev
interpret env (Ops (TailExpr e)) = do
  ev <- interpretU env e
  reduceTail ev
interpret env (Ops (ConsExpr h t)) = do
  hv <- interpretU env h
  tv <- interpretU env t
  reduceCons hv tv
interpret env (Ops (AndExpr l r)) = do
  lv <- interpretU env l
  rv <- interpretU env r
  reduceAnd lv rv
interpret env (Ops (NotExpr e)) = do
  ev <- interpretU env e
  reduceNot ev
interpret env (Ops (VarExpr i)) = reduceValue env i
interpret _ (Lit l) = mrgReturn l

interpretStmt :: Stmt -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmt (DefineStmt i expr) = StateT $ \st -> mrgFmap (\t -> (UnitLit, (i, mrgSingle t) : st)) $ interpretU st expr
interpretStmt (ValueStmt expr) = StateT $ \env -> mrgFmap (,env) $ mrgLift expr >>= interpret env

interpretStmtU :: UnionM Stmt -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmtU stmt = (lift . lift) stmt >>= interpretStmt

interpretStmtList :: [Stmt] -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmtList [] = mrgReturn UnitLit
interpretStmtList [x] = interpretStmt x
interpretStmtList (x : xs) = interpretStmt x >>~ interpretStmtList xs

interpretStmtListU :: [UnionM Stmt] -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmtListU [] = mrgReturn UnitLit
interpretStmtListU [x] = interpretStmtU x
interpretStmtListU (x : xs) = interpretStmtU x >>~ interpretStmtListU xs

interpretStmtUListU :: UnionM [UnionM Stmt] -> StateT ExecutingEnv (ExceptT Error UnionM) LitExpr
interpretStmtUListU stmtlst = (lift . lift) stmtlst >>= interpretStmtListU

checkAndInterpretStmtList :: [Stmt] -> ExceptT Error UnionM LitExpr
checkAndInterpretStmtList st = evalStateT (typeCheckStmtList st) [] >>~ evalStateT (interpretStmtList st) []

checkAndInterpretStmtUListU :: UnionM [UnionM Stmt] -> ExceptT Error UnionM LitExpr
checkAndInterpretStmtUListU st = evalStateT (typeCheckStmtUListU st) [] >>~ evalStateT (interpretStmtUListU st) []
