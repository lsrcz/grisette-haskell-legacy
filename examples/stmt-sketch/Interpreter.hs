{-# LANGUAGE TemplateHaskell #-}
module Interpreter where

import Control.Monad.Except
import Control.Monad.State
import DataStructures
import Generics.Deriving
import Grisette hiding (AssertionError)

data SValue
  = SInt SymInteger
  | SBool SymBool
  | SUnit
  deriving (Show, Eq, Generic)
  deriving (SEq SymBool, Mergeable SymBool) via (Default SValue)

$(makeUnionMWrapper "u" ''SValue)

type Env = [(SIdentifier, UnionM SValue)]

lookupEnvU :: UnionM Env -> SIdentifier -> ExceptT Errors UnionM SValue
lookupEnvU env i = lift env >>= \e -> lookupEnv e i

lookupEnv :: Env -> SIdentifier -> ExceptT Errors UnionM SValue
lookupEnv [] _ = throwError UndefinedVariable
lookupEnv ((x, xv) : xs) i = mrgIf (x ==~ i) (lift xv) (lookupEnv xs i)

data Errors
  = AssertionError
  | BadType
  | UndefinedVariable
  deriving (Show, Eq, Generic)
  deriving (SEq SymBool, Mergeable SymBool) via (Default Errors)

instance TransformError Errors Errors where
  transformError = id

interpretExprU :: UnionM Env -> UnionM SymbExpr -> ExceptT Errors UnionM SValue
interpretExprU env x = lift x >>= interpretExpr env

interpretBop ::
  UnionM Env ->
  UnionM SymbExpr ->
  UnionM SymbExpr ->
  (SValue -> SValue -> ExceptT Errors UnionM SValue) ->
  ExceptT Errors UnionM SValue
interpretBop env l r f = do
  lv <- interpretExprU env l
  rv <- interpretExprU env r
  f lv rv

interpretExpr :: UnionM Env -> SymbExpr -> ExceptT Errors UnionM SValue
interpretExpr _ (SIntConstantExpr i) = uSInt i
interpretExpr _ (SBoolConstantExpr b) = uSBool b
interpretExpr env (SLtExpr l r) = interpretBop env l r $
  curry $ \case
    (SInt x, SInt y) -> uSBool $ x <~ y
    _ -> throwError BadType
interpretExpr env (SEqExpr l r) = interpretBop env l r $
  curry $ \case
    (SInt x, SInt y) -> uSBool $ x ==~ y
    (SBool x, SBool y) -> uSBool $ x ==~ y
    _ -> throwError BadType
interpretExpr env (SAndExpr l r) = interpretBop env l r $
  curry $ \case
    (SBool x, SBool y) -> uSBool $ x &&~ y
    _ -> throwError BadType
interpretExpr env (SOrExpr l r) = interpretBop env l r $
  curry $ \case
    (SBool x, SBool y) -> uSBool $ x ||~ y
    _ -> throwError BadType
interpretExpr env (SAddExpr l r) = interpretBop env l r $
  curry $ \case
    (SInt x, SInt y) -> uSInt $ x + y
    _ -> throwError BadType
interpretExpr env (SSubExpr l r) = interpretBop env l r $
  curry $ \case
    (SInt x, SInt y) -> uSInt $ x - y
    _ -> throwError BadType
interpretExpr env (SMulExpr l r) = interpretBop env l r $
  curry $ \case
    (SInt x, SInt y) -> uSInt $ x * y
    _ -> throwError BadType
interpretExpr env (SVarExpr v) = lookupEnvU env v

interpretStmt :: SymbStmt -> StateT (UnionM Env) (ExceptT Errors UnionM) ()
interpretStmt (SAssignStmt i e) = StateT $
  \st ->
    mrgFmap (\t -> ((), mrgFmap (\s -> (i, mrgReturn t) : s) st)) $
      interpretExprU st e
interpretStmt (SAssertStmt v) = do
  cond <- StateT $ \st -> mrgFmap (,st) $ interpretExprU st v
  case cond of
    SBool sym -> gassertWithError AssertionError sym
    _ -> throwError BadType
interpretStmt (SIfStmt v l r) = do
  cond <- StateT $ \st -> mrgFmap (,st) $ interpretExprU st v
  case cond of
    SBool sym -> mrgIf sym (interpretStmtList l) (interpretStmtList r)
    _ -> throwError BadType

interpretStmtList :: [SymbStmt] -> StateT (UnionM Env) (ExceptT Errors UnionM) ()
interpretStmtList = foldM (\_ stmt -> interpretStmt stmt) ()

interpretProgram :: SymbProgram -> ExceptT Errors UnionM ()
interpretProgram (SymbProgram s) = evalStateT (interpretStmtList s) (mrgReturn [])

data DoSynthesis = DoSynthesis

instance SolverTranslation DoSynthesis Errors () where
  errorTranslation _ _ = False
  valueTranslation _ _ = conc True

data GetTypeError = GetTypeError

instance SolverTranslation GetTypeError Errors () where
  errorTranslation _ BadType = True
  errorTranslation _ _ = False
  valueTranslation _ _ = conc False

synthesis ::
  (SolverTranslation method Errors ()) =>
  method ->
  GrisetteSMTConfig i ->
  SymbProgram ->
  IO (Maybe Program)
synthesis method config s = do
  m <- solveWithTranslation method config (interpretProgram s)
  case m of
    Left _ -> return Nothing
    Right mo -> return $ toCon $ evaluate True mo s
