{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Interpreter where
import Grisette.Data.SymPrim
import DataStructures
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SOrd
import GHC.Generics
import Grisette.Data.Class.Bool
import Control.Monad.Except
import Grisette.Control.Monad
import Grisette.Data.Class.SimpleMergeable
import Control.Monad.State
import Grisette.Data.Functor (mrgFmap)
import Grisette.Data.Class.Error
import Grisette.Data.SMT.Solving
import Grisette.Data.SMT.Config
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.PrimWrapper

data SValue
  = SInt SymInteger
  | SBool SymBool
  | SUnit
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool)

type Env = [(SIdentifier, UnionM SValue)]

lookupEnvU :: UnionM Env -> SIdentifier -> ExceptT Errors UnionM SValue
lookupEnvU env i = lift env >>= \e -> lookupEnv e i

lookupEnv :: Env -> SIdentifier -> ExceptT Errors UnionM SValue
lookupEnv [] _ = throwError InvalidProgram
lookupEnv ((x,xv):xs) i = mrgGuard (x ==~ i) (lift xv) (lookupEnv xs i)

data Errors
  = AssertionError
  | InvalidProgram
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool)

instance TransformError Errors Errors where
  transformError = id

interpretExprU :: UnionM Env -> UnionM SymbExpr -> ExceptT Errors UnionM SValue
interpretExprU env x = lift x >>= interpretExpr env

interpretBop :: UnionM Env -> UnionM SymbExpr -> UnionM SymbExpr ->
   (SValue -> SValue -> ExceptT Errors UnionM SValue) -> ExceptT Errors UnionM SValue
interpretBop env l r f = do
  lv <- interpretExprU env l
  rv <- interpretExprU env r
  f lv rv

interpretExpr :: UnionM Env -> SymbExpr -> ExceptT Errors UnionM SValue
interpretExpr _ (SIntConstantExpr i) = mrgReturn $ SInt i
interpretExpr _ (SBoolConstantExpr b) = mrgReturn $ SBool b
interpretExpr env (SLtExpr l r) = interpretBop env l r $ curry $ \case
  (SInt x, SInt y) -> mrgReturn $ SBool $ x <~ y
  _ -> throwError InvalidProgram
interpretExpr env (SEqExpr l r) = interpretBop env l r $ curry $ \case
  (SInt x, SInt y) -> mrgReturn $ SBool $ x ==~ y
  (SBool x, SBool y) -> mrgReturn $ SBool $ x ==~ y
  _ -> throwError InvalidProgram
interpretExpr env (SAndExpr l r) = interpretBop env l r $ curry $ \case
  (SBool x, SBool y) -> mrgReturn $ SBool $ x &&~ y
  _ -> throwError InvalidProgram
interpretExpr env (SOrExpr l r) = interpretBop env l r $ curry $ \case
  (SBool x, SBool y) -> mrgReturn $ SBool $ x ||~ y
  _ -> throwError InvalidProgram
interpretExpr env (SAddExpr l r) = interpretBop env l r $ curry $ \case
  (SInt x, SInt y) -> mrgReturn $ SInt $ x + y
  _ -> throwError InvalidProgram
interpretExpr env (SSubExpr l r) = interpretBop env l r $ curry $ \case
  (SInt x, SInt y) -> mrgReturn $ SInt $ x - y
  _ -> throwError InvalidProgram
interpretExpr env (SMulExpr l r) = interpretBop env l r $ curry $ \case
  (SInt x, SInt y) -> mrgReturn $ SInt $ x * y
  _ -> throwError InvalidProgram
interpretExpr env (SVarExpr v) = lookupEnvU env v

interpretStmt :: SymbStmt -> StateT (UnionM Env) (ExceptT Errors UnionM) ()
interpretStmt (SAssignStmt i e) = StateT $
  \st -> mrgFmap (\t -> ((), mrgFmap (\s -> (i, mrgSingle t) : s) st)) $
    interpretExprU st e
interpretStmt (SAssertStmt v) = do
  cond <- StateT $ \st -> mrgFmap (,st) $ interpretExprU st v
  case cond of
    SBool sym -> gassertWithError AssertionError sym
    _ -> throwError InvalidProgram
interpretStmt (SIfStmt v l r) = do
  cond <- StateT $ \st -> mrgFmap (,st) $ interpretExprU st v
  case cond of
    SBool sym -> mrgGuard sym (interpretStmtList l) (interpretStmtList r)
    _ -> throwError InvalidProgram

interpretStmtList :: [SymbStmt] -> StateT (UnionM Env) (ExceptT Errors UnionM) ()
interpretStmtList = foldM (\_ stmt -> interpretStmt stmt) ()

interpretProgram :: SymbProgram -> ExceptT Errors UnionM ()
interpretProgram (SymbProgram s) = evalStateT (interpretStmtList s) (mrgSingle [])

synthesis :: GrisetteSMTConfig i -> SymbProgram -> IO (Maybe Program)
synthesis config s = do
  m <- solveWith config $ getSingle $ mrgFmap (\case
    Left _ -> conc False
    Right _ -> conc True) $ runExceptT (interpretProgram s)
  case m of
    Left _ -> return Nothing
    Right mo -> return $ toCon $ symeval True mo s

