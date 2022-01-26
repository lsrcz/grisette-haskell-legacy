{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PippiInterpreter2 where

import Control.Monad.Except
import Control.Monad.State
import GHC.Generics
import Grisette.Control.Monad
import Grisette.Control.Monad.Trans
import Grisette.Control.Monad.UnionM
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.SymGen
import Grisette.Data.Functor
import Grisette.Data.Prim.Model
import Grisette.Data.SymPrim
import Grisette.Data.Class.ToSym

wrapInParens :: String -> String
wrapInParens input = "(" ++ input ++ ")"

--
-- | Data Types
--
data MovingExpr 
   = Coord CoordExpr
   | Moving MovingOpExpr
   | MovingVarExpr   SymInteger -- (conc 1)
   deriving (Generic)

instance Show MovingExpr where
  show (Coord c) = wrapInParens $ show c 
  show (Moving op) = wrapInParens $ show op
  show (MovingVarExpr v) = wrapInParens $ "var:" ++ show v

instance Mergeable SymBool MovingExpr
instance ToSym MovingExpr MovingExpr
instance SymEval Model MovingExpr

data CoordExpr 
  = CoordLit SymInteger SymInteger
  | UnitLit -- ()
  deriving (Generic)

instance Show CoordExpr where
  show (CoordLit x y) = "Coord {x: " ++ (show x) ++ ", y: " ++ (show y) ++ ")"
  show UnitLit = "UnitLit"

instance Mergeable SymBool CoordExpr
instance ToSym CoordExpr CoordExpr
instance SymEval Model CoordExpr
instance SEq (Sym Bool) CoordExpr

data MovingOpExpr
   = MoveUp    (UnionM MovingExpr)
   | MoveDown  (UnionM MovingExpr)
   | MoveLeft  (UnionM MovingExpr)
   | MoveRight (UnionM MovingExpr)
   deriving (Generic)

instance Show MovingOpExpr where 
  show (MoveUp e) = wrapInParens $ "MoveUp " ++ (wrapInParens $ show e)
  show (MoveDown e) = wrapInParens $ "MoveDown" ++ (wrapInParens $ show e)
  show (MoveLeft e) = wrapInParens $ "MoveLeft" ++ (wrapInParens $ show e)
  show (MoveRight e) = wrapInParens $ "MoveRight" ++ (wrapInParens $ show e)

instance Mergeable SymBool MovingOpExpr
instance ToSym MovingOpExpr MovingOpExpr
instance SymEval Model MovingOpExpr

data MovingStmt
  = MovingDefineStmt SymInteger (UnionM MovingExpr)
  | MovingValueStmt (UnionM MovingExpr)
  deriving (Generic)

instance Show MovingStmt where
  show (MovingDefineStmt name e) = wrapInParens $ show name ++ " = " ++ show e 
  show (MovingValueStmt e) = wrapInParens $ "return " ++ show e

instance Mergeable SymBool MovingStmt
instance ToSym MovingStmt MovingStmt
instance SymEval Model MovingStmt

data MovingExprSpec = MovingExprSpec
  { mvmntExprDepth :: Integer }
  deriving (Show)

type ExecutingEnv = [(SymInteger, UnionM CoordExpr)]
type TypingEnv = [(SymInteger, UnionM MovingType)]

--
-- | SymGen Instances Without Arg
--
instance SymGen SymBool () CoordExpr where
  genSymIndexed _ = do
    x <- genSymSimpleIndexed @SymBool ()
    y <- genSymSimpleIndexed @SymBool ()
    choose (CoordLit x y) [UnitLit]
    

instance SymGen SymBool MovingExprSpec MovingOpExpr where
  genSymIndexed (MovingExprSpec d) = do
    e <- genSymIndexed (MovingExprSpec (d - 1))
    choose
       (MoveUp e)
      [ MoveDown e,
        MoveLeft e,
        MoveRight e
      ]

instance SymGen SymBool MovingExprSpec MovingExpr where
  genSymIndexed e@(MovingExprSpec d) =
    merge
      <$> if d <= 0
        then do
          coord <- genSymSimpleIndexed @SymBool ()
          v <- genSymSimpleIndexed @SymBool ()
          chooseU (Coord <$> coord) [MovingVarExpr <$> v]
        else do
          coord <- genSymIndexed ()
          moving <- genSymIndexed e
          v <- genSymSimpleIndexed @SymBool ()
          chooseU (Coord <$> coord) [Moving <$> moving, MovingVarExpr <$> v]

instance SymGen SymBool MovingExprSpec MovingStmt where
  genSymIndexed e = do
    expr <- genSymIndexed @SymBool e
    vari <- genSymSimpleIndexed @SymBool ()
    choose (MovingDefineStmt vari expr) [MovingValueStmt expr]

--
-- | SymGen Instances With Arg
--
instance SymGen SymBool (MovingExprSpec, CoordExpr) MovingOpExpr where
  genSymIndexed ((MovingExprSpec d), arg) = do
    e <- genSymIndexed ((MovingExprSpec (d - 1)), arg)
    choose
       (MoveUp e)
      [ MoveDown e,
        MoveLeft e,
        MoveRight e
      ]

instance SymGen SymBool (MovingExprSpec, CoordExpr) MovingExpr where
  genSymIndexed (e@(MovingExprSpec d), arg) =
    merge
      <$> if d <= 0
        then do
          let coord = toSym arg
          v <- genSymSimpleIndexed @SymBool ()
          choose (Coord coord) [MovingVarExpr v]
        else do
          let coord = toSym arg
          moving <- genSymIndexed (e, arg)
          chooseU (Coord <$> coord) [Moving <$> moving]

instance SymGen SymBool (MovingExprSpec, CoordExpr) MovingStmt where
  genSymIndexed (e, arg) = do
    expr <- genSymIndexed @SymBool (e, arg)
    vari <- genSymSimpleIndexed @SymBool ()
    choose (MovingDefineStmt vari expr) [MovingValueStmt expr]

--
-- | SymGen Instances With Function Arguments
--
instance SymGen SymBool () (CoordExpr -> SymInteger) where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple SymBool () (CoordExpr -> SymInteger) where
  genSymSimpleIndexed _ = do
    v <- genSymSimpleIndexed @SymBool ()
    return $ const v


instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingOpExpr) where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingOpExpr) where
  genSymSimpleIndexed (MovingExprSpec d) = do
    e <- genSymSimpleIndexed @SymBool (MovingExprSpec (d - 1))
    r <- choose
            ( mrgSingle . MoveUp    . e)
            [ mrgSingle . MoveDown  . e,
              mrgSingle . MoveLeft  . e,
              mrgSingle . MoveRight . e
            ]
    return $ getSingle @SymBool r

instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingExpr) where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingExpr) where
  genSymSimpleIndexed e@(MovingExprSpec d) =
   if d <= 0
        then do
          v <- genSymSimpleIndexed @SymBool ()

          r <- choose (mrgSingle . Coord) [mrgSingle . MovingVarExpr . v]
          return $ getSingle @SymBool r

        else do
          
          moving <- genSymSimpleIndexed @SymBool e
          v <- genSymSimpleIndexed @SymBool ()

          r <- choose
                  ( mrgSingle . Coord)
                  [ mrgSingle . MovingVarExpr . v,
                    (mrgFmap    Moving)       . moving
                  ]
          return $ getSingle @SymBool r

-- might need to figure out later.... <3 
-- instance SymGen SymBool MovingExprSpec (CoordExpr -> MovingStmt) where
--   genSymIndexed e = do
--     expr <- genSymIndexed @SymBool e
--     vari <- genSymSimpleIndexed @SymBool ()
--     choose (MovingDefineStmt vari expr) [MovingValueStmt expr]


--
-- | Errors
--

data MovingError
  = MovingTyper MovingTyperError
  | MovingRuntime MovingRuntimeError
  deriving (Generic, Show)

instance Mergeable (Sym Bool) MovingError
instance SymEval Model MovingError

data MovingTyperError
  = MovingTypeVarNotFound
  | TypeMismatch
  deriving (Generic, Show)
instance Mergeable (Sym Bool) MovingTyperError
instance SymEval Model MovingTyperError

data MovingRuntimeError
  = MovingRuntimeVarNotFound
  | MovingRuntimeTypeMismatch
  | MovingRuntimeRuntimeError
  deriving (Generic, Show)

instance Mergeable (Sym Bool) MovingRuntimeError
instance SymEval Model MovingRuntimeError

data MovingType
  = UnitType
  | CoordType
  deriving (Generic, Show, Eq)

instance Mergeable (Sym Bool) MovingType

typeCheckU :: TypingEnv -> UnionM MovingExpr -> ExceptT MovingError UnionM MovingType
typeCheckU env u = lift u >>= typeCheck env

typeCheck :: TypingEnv -> MovingExpr -> ExceptT MovingError UnionM MovingType
typeCheck _ (Coord (CoordLit _ _)) = mrgReturn CoordType
typeCheck _ (Coord UnitLit) = mrgReturn UnitType
typeCheck env (Moving (MoveUp e)) = do
  et <- typeCheckU env e
  merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
typeCheck env (Moving (MoveDown e)) = do
  et <- typeCheckU env e
  merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
typeCheck env (Moving (MoveLeft e)) = do
  et <- typeCheckU env e
  merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
typeCheck env (Moving (MoveRight e)) = do
  et <- typeCheckU env e
  merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
typeCheck env (MovingVarExpr i) = resolveEnv env i
  where
    resolveEnv [] _ = merge $ throwError $ MovingTyper MovingTypeVarNotFound
    resolveEnv ((hdi, hdt) : tl) i1 = mrgIf @SymBool (hdi ==~ i1) (lift hdt) $ resolveEnv tl i1

typeCheckStmt :: MovingStmt -> StateT TypingEnv (ExceptT MovingError UnionM) MovingType
typeCheckStmt (MovingDefineStmt i expr) = StateT $ \st -> mrgFmap (\t -> (UnitType, (i, mrgSingle t) : st)) $ typeCheckU st expr
typeCheckStmt (MovingValueStmt expr) = StateT $ \st -> mrgFmap (,st) $ mrgLift expr >>= typeCheck st

typeCheckStmtU :: UnionM MovingStmt -> StateT TypingEnv (ExceptT MovingError UnionM) MovingType
typeCheckStmtU stmt = (lift . lift) stmt >>= typeCheckStmt

typeCheckStmtList :: [MovingStmt] -> StateT TypingEnv (ExceptT MovingError UnionM) MovingType
typeCheckStmtList [] = mrgReturn UnitType
typeCheckStmtList [x] = typeCheckStmt x
typeCheckStmtList (x : xs) = typeCheckStmt x >>~ typeCheckStmtList xs

typeCheckStmtListU :: [UnionM MovingStmt] -> StateT TypingEnv (ExceptT MovingError UnionM) MovingType
typeCheckStmtListU [] = mrgReturn UnitType
typeCheckStmtListU [x] = typeCheckStmtU x
typeCheckStmtListU (x : xs) = typeCheckStmtU x >>~ typeCheckStmtListU xs

typeCheckStmtUListU :: UnionM [UnionM MovingStmt] -> StateT TypingEnv (ExceptT MovingError UnionM) MovingType
typeCheckStmtUListU u = (lift . lift) u >>= typeCheckStmtListU

--
-- | Reducing 
--
reduceMoveUp :: CoordExpr -> ExceptT MovingError UnionM CoordExpr
reduceMoveUp (CoordLit x y) = do
  mrgReturn $ CoordLit x (y - 1)
reduceMoveUp _ = merge $ throwError $ MovingRuntime MovingRuntimeTypeMismatch

reduceMoveDown :: CoordExpr -> ExceptT MovingError UnionM CoordExpr
reduceMoveDown (CoordLit x y) = do
  mrgReturn $ CoordLit x (y + 1)
reduceMoveDown _ = merge $ throwError $ MovingRuntime MovingRuntimeTypeMismatch

reduceMoveLeft :: CoordExpr -> ExceptT MovingError UnionM CoordExpr
reduceMoveLeft (CoordLit x y) = do
  mrgReturn $ CoordLit (x - 1) y
reduceMoveLeft _ = merge $ throwError $ MovingRuntime MovingRuntimeTypeMismatch

reduceMoveRight :: CoordExpr -> ExceptT MovingError UnionM CoordExpr
reduceMoveRight (CoordLit x y) = do
  mrgReturn $ CoordLit (x + 1) y
reduceMoveRight _ = merge $ throwError $ MovingRuntime MovingRuntimeTypeMismatch

reduceValue :: ExecutingEnv -> SymInteger -> ExceptT MovingError UnionM CoordExpr
reduceValue [] _ = merge $ throwError $ MovingRuntime MovingRuntimeVarNotFound
reduceValue ((hdi, hdv) : tl) h = mrgIf @SymBool (hdi ==~ h) (lift hdv) $ reduceValue tl h


--
-- | Interpreting 
--
interpretU :: ExecutingEnv -> UnionM MovingExpr -> ExceptT MovingError UnionM CoordExpr
interpretU env u = mrgLift u >>= interpret env

interpret :: ExecutingEnv -> MovingExpr -> ExceptT MovingError UnionM CoordExpr
interpret _ (Coord c) = mrgReturn c
interpret env (Moving (MoveUp e)) = do
  ev <- interpretU env e
  reduceMoveUp ev
interpret env (Moving (MoveDown e)) = do
  ev <- interpretU env e
  reduceMoveDown ev
interpret env (Moving (MoveLeft e)) = do
  ev <- interpretU env e
  reduceMoveLeft ev
interpret env (Moving (MoveRight e)) = do
  ev <- interpretU env e
  reduceMoveRight ev
interpret env (MovingVarExpr i) = reduceValue env i

interpretStmt :: MovingStmt -> StateT ExecutingEnv (ExceptT MovingError UnionM) CoordExpr
interpretStmt (MovingDefineStmt i expr) = StateT $ \st -> mrgFmap (\t -> (UnitLit, (i, mrgSingle t) : st)) $ interpretU st expr
interpretStmt (MovingValueStmt expr) = StateT $ \env -> mrgFmap (,env) $ mrgLift expr >>= interpret env

interpretStmtU :: UnionM MovingStmt -> StateT ExecutingEnv (ExceptT MovingError UnionM) CoordExpr
interpretStmtU stmt = (lift . lift) stmt >>= interpretStmt

interpretStmtList :: [MovingStmt] -> StateT ExecutingEnv (ExceptT MovingError UnionM) CoordExpr
interpretStmtList [] = mrgReturn UnitLit
interpretStmtList [x] = interpretStmt x
interpretStmtList (x : xs) = interpretStmt x >>~ interpretStmtList xs

interpretStmtListU :: [UnionM MovingStmt] -> StateT ExecutingEnv (ExceptT MovingError UnionM) CoordExpr
interpretStmtListU [] = mrgReturn UnitLit
interpretStmtListU [x] = interpretStmtU x
interpretStmtListU (x : xs) = interpretStmtU x >>~ interpretStmtListU xs

interpretStmtUListU :: UnionM [UnionM MovingStmt] -> StateT ExecutingEnv (ExceptT MovingError UnionM) CoordExpr
interpretStmtUListU stmtlst = (lift . lift) stmtlst >>= interpretStmtListU

checkAndInterpretStmtList :: [MovingStmt] -> ExceptT MovingError UnionM CoordExpr
checkAndInterpretStmtList st = evalStateT (typeCheckStmtList st) [] >>~ evalStateT (interpretStmtList st) []

checkAndInterpretStmtUListU :: UnionM [UnionM MovingStmt] -> ExceptT MovingError UnionM CoordExpr
checkAndInterpretStmtUListU st = evalStateT (typeCheckStmtUListU st) [] >>~ evalStateT (interpretStmtUListU st) []







-- The following should lie in Grisette lib
extractArgFromListOfFunc :: [a -> b] -> a -> [b]
extractArgFromListOfFunc l a = (\x -> x a) <$> l

extractArgFromUnionMBaseOfFunc :: (SymBoolOp bool, Mergeable bool b) => UnionMBase bool (a -> b) -> a -> UnionMBase bool b
extractArgFromUnionMBaseOfFunc l a = mrgFmap (\x -> x a) l

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec (a -> b), Mergeable bool b) =>
  SymGen bool (ListSpec spec) (a -> UnionMBase bool [b]) where
  genSymIndexed v = genSymSimpleIndexed @bool v

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec (a -> b), Mergeable bool b) =>
  SymGenSimple bool (ListSpec spec) (a -> UnionMBase bool [b])
  where
  genSymSimpleIndexed spec = do
    l <- genSymIndexed @bool @(ListSpec spec) @[a -> b] spec
    return $ extractArgFromUnionMBaseOfFunc (extractArgFromListOfFunc <$> l)
-- The previous section should lie in Grisette lib