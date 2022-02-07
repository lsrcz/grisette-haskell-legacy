{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DeriveAnyClass #-}
-- {-# LANGUAGE OverlappingInstances #-}
-- {-# LANGUAGE FlexibleInstances #-}

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
import Grisette.Data.Class.ToCon
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
   = Coord (UnionM CoordExpr)
   | Moving (UnionM MovingOpExpr)
  --  = Coord CoordExpr
  --  | Moving MovingOpExpr
   | MovingVarExpr SymInteger
   deriving (Generic, Show, Eq, ToSym ConcMovingExpr)

instance Mergeable SymBool MovingExpr
instance ToSym MovingExpr MovingExpr
instance SymEval Model MovingExpr

data CoordExpr 
  = CoordLit SymInteger SymInteger
  | UnitLit
  deriving (Generic, Show, Eq, ToSym ConcCoordExpr)

instance Mergeable SymBool CoordExpr
instance ToSym CoordExpr CoordExpr
instance SymEval Model CoordExpr
instance SEq (Sym Bool) CoordExpr

data MovingOpExpr
   = MoveUp    (UnionM MovingExpr)
   | MoveDown  (UnionM MovingExpr)
   | MoveLeft  (UnionM MovingExpr)
   | MoveRight (UnionM MovingExpr)
   deriving (Generic, Show, Eq, ToSym ConcMovingOpExpr)

instance Mergeable SymBool MovingOpExpr
instance ToSym MovingOpExpr MovingOpExpr
instance SymEval Model MovingOpExpr

data MovingStmt
  = MovingDefineStmt SymInteger (UnionM MovingExpr)
  | MovingValueStmt (UnionM MovingExpr)
  deriving (Generic, Show, Eq, ToSym ConcMovingStmt)

instance Mergeable SymBool MovingStmt
instance ToSym MovingStmt MovingStmt
instance SymEval Model MovingStmt

data MovingExprSpec = MovingExprSpec {mvmntExprDepth :: Integer}
  deriving (Show)

type ExecutingEnv = [(SymInteger, UnionM CoordExpr)]
type TypingEnv = [(SymInteger, UnionM MovingType)]


--
-- | Concrete Data Types
--
data ConcMovingExpr 
   = ConcCoord ConcCoordExpr
   | ConcMoving ConcMovingOpExpr
   | ConcMovingVarExpr Integer
   deriving (Generic, Eq, ToCon MovingExpr)

instance Show ConcMovingExpr where
  show (ConcCoord c) = show c 
  show (ConcMoving op) = show op
  show (ConcMovingVarExpr v) = "var:" ++ show v

data ConcCoordExpr 
  = ConcCoordLit Integer Integer
  | ConcUnitLit
  deriving (Generic, Eq, ToCon CoordExpr)

instance Show ConcCoordExpr where
  show (ConcCoordLit x y) = "Coord {x: " ++ (show x) ++ ", y: " ++ (show y) ++ "}"
  show ConcUnitLit = "UnitLit"

data ConcMovingOpExpr
   = ConcMoveUp    ConcMovingExpr
   | ConcMoveDown  ConcMovingExpr
   | ConcMoveLeft  ConcMovingExpr
   | ConcMoveRight ConcMovingExpr
   deriving (Generic, Eq, ToCon MovingOpExpr)

instance Show ConcMovingOpExpr where 
  show (ConcMoveUp e) = "MoveUp " ++ (wrapInParens $ show e)
  show (ConcMoveDown e) = "MoveDown " ++ (wrapInParens $ show e)
  show (ConcMoveLeft e) = "MoveLeft " ++ (wrapInParens $ show e)
  show (ConcMoveRight e) = "MoveRight " ++ (wrapInParens $ show e)

data ConcMovingStmt
  = ConcMovingDefineStmt Integer ConcMovingExpr
  | ConcMovingValueStmt  ConcMovingExpr
  deriving (Generic, ToCon MovingStmt)

instance Show ConcMovingStmt where
  show (ConcMovingDefineStmt name e) = "var:" ++ show name ++ " := " ++ show e 
  show (ConcMovingValueStmt e) = "return " ++ (wrapInParens $ show e)

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
    
    choose (MoveUp e)
          [ MoveDown e,
            MoveLeft e,
            MoveRight e
          ]

instance SymGen SymBool MovingExprSpec MovingExpr where
  genSymIndexed spec@(MovingExprSpec d) = -- merge <$> 
    if d <= 0
      then do
        -- coord   <- genSymSimpleIndexed @SymBool ()
        -- varName <- genSymSimpleIndexed @SymBool ()
        -- chooseU (Coord <$> coord) [MovingVarExpr <$> varName]
        
        coord   <- genSymIndexed @SymBool ()
        varName <- genSymSimpleIndexed @SymBool ()

        choose (Coord coord) [MovingVarExpr varName]
      
      else do
        coord   <- genSymIndexed @SymBool ()
        moving  <- genSymIndexed @SymBool spec
        varName <- genSymSimpleIndexed @SymBool ()
        
        choose (Coord coord) [Moving moving, MovingVarExpr varName]

instance SymGen SymBool MovingExprSpec MovingStmt where
  genSymIndexed spec = do
    e       <- genSymIndexed @SymBool spec
    varName <- genSymSimpleIndexed @SymBool ()
    
    choose (MovingDefineStmt varName e) [MovingValueStmt e]

--
-- | SymGen Instances With Arg
--
instance SymGen SymBool (MovingExprSpec, MovingExpr) MovingOpExpr where
  genSymIndexed ((MovingExprSpec d), arg) = do
    e <- genSymIndexed ((MovingExprSpec (d - 1)), arg)
    
    choose (MoveUp e)
          [ MoveDown e,
            MoveLeft e,
            MoveRight e
          ]

instance SymGen SymBool (MovingExprSpec, MovingExpr) MovingExpr where
  genSymIndexed (spec@(MovingExprSpec d), arg) = case arg of
    (Coord coord) -> -- merge <$>
      if d <= 0
        then do
          -- mrgReturn $ Coord coord
          choose (Coord coord) []
          -- return $ mrgSingle $ Coord $ toSym coord
        else do
          moving <- genSymIndexed @SymBool (spec, (Coord coord))
          
          -- chooseU (Coord <$> (toSym coord)) [Moving <$> moving]
          choose (Coord coord) [Moving moving]
    
    (MovingVarExpr var) -> -- merge <$> 
      if d <= 0
        then do
          -- mrgReturn $ MovingVarExpr var
          choose (MovingVarExpr var) []
        else do
          moving <- genSymIndexed @SymBool (spec, MovingVarExpr var)
          
          -- chooseU (MovingVarExpr <$> (toSym var)) [Moving <$> moving]
          choose (MovingVarExpr var) [Moving moving]
    
    _ -> error "shouldn't ever be here!"
    
-- TODO this might need to be implemented later
-- instance SymGen SymBool (MovingExprSpec, MovingExpr) MovingStmt where
--   genSymIndexed (e, arg) = case arg of
--     (Coord coord) -> do
--       ex <- genSymIndexed @SymBool (e, (Coord coord))
--       varName <- genSymSimpleIndexed @SymBool ()
--       choose (MovingDefineStmt varName ex) [MovingValueStmt ex]
--     (MovingVarExpr var) -> undefined
--     _ -> error "shouldn't ever be here!"
    

--
-- | SymGen Instances With Function Arguments
--
-- instance SymGen SymBool () (CoordExpr -> SymInteger) where
--   genSymIndexed v = genSymSimpleIndexed @SymBool v

-- instance SymGenSimple SymBool () (CoordExpr -> SymInteger) where
--   genSymSimpleIndexed _ = do
--     v <- genSymSimpleIndexed @SymBool ()
--     return $ const v


-- instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingOpExpr) where
--   genSymIndexed v = genSymSimpleIndexed @SymBool v

-- instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingOpExpr) where
--   genSymSimpleIndexed (MovingExprSpec d) = do
--     e <- genSymSimpleIndexed @SymBool (MovingExprSpec (d - 1))
--     r <- choose
--             ( mrgSingle . MoveUp    . e)
--             [ mrgSingle . MoveDown  . e,
--               mrgSingle . MoveLeft  . e,
--               mrgSingle . MoveRight . e
--             ]
--     return $ getSingle @SymBool r

-- instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingExpr) where
--   genSymIndexed v = genSymSimpleIndexed @SymBool v

-- instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingExpr) where
--   genSymSimpleIndexed spec@(MovingExprSpec d) =
--    if d <= 0
--     then do
--       v <- genSymSimpleIndexed @SymBool ()

--       r <- choose (mrgSingle . Coord) 
--                   [mrgSingle . MovingVarExpr . v]
--       return $ getSingle @SymBool r

--     else do
--       moving <- genSymSimpleIndexed @SymBool spec
--       v <- genSymSimpleIndexed @SymBool ()

--       r <- choose
--               ( mrgSingle . Coord)
--               [ mrgSingle . MovingVarExpr . v,
--                 (mrgFmap    Moving)       . moving
--               ]
--       return $ getSingle @SymBool r

-- instance SymGen SymBool MovingExprSpec (CoordExpr -> UnionM MovingStmt) where
--   genSymIndexed v = genSymSimpleIndexed @SymBool v

-- TODO might need to figure out later.... <3 
-- instance SymGenSimple SymBool MovingExprSpec (CoordExpr -> UnionM MovingStmt) where
--   genSymSimpleIndexed e = do

--     expr <- genSymIndexed @SymBool e
--     vari <- genSymSimpleIndexed @SymBool ()

--     r <- choose 
--           (mrgSingle . MovingDefineStmt . vari . expr) 
--           [mrgSingle . MovingValueStmt expr]

--     return $ getSingle @SymBool r


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
-- typeCheckU env e = do
--   concE <- lift e
--   case concE of
--     _ -> typeCheck env concE

typeCheck :: TypingEnv -> MovingExpr -> ExceptT MovingError UnionM MovingType
typeCheck _ (Coord coord) = do
  concCoord <- lift coord
  case concCoord of
    UnitLit -> mrgReturn UnitType
    (CoordLit _ _) -> mrgReturn CoordType
typeCheck env (Moving symExpr) = do
  concMove <- lift symExpr
  case concMove of 
    (MoveUp e) -> movementTypeCheck env e
    (MoveDown e) -> movementTypeCheck env e
    (MoveLeft e) -> movementTypeCheck env e
    (MoveRight e) -> movementTypeCheck env e
typeCheck env (MovingVarExpr i) = resolveEnv env i
-- typeCheck _ (Coord UnitLit) = mrgReturn UnitType
-- typeCheck env (Moving (MoveDown e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheck env (Moving (MoveLeft e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheck env (Moving (MoveRight e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheck env (MovingVarExpr i) = resolveEnv env i
  where
    resolveEnv [] _ = merge $ throwError $ MovingTyper MovingTypeVarNotFound
    resolveEnv ((hdi, hdt) : tl) i1 = mrgIf @SymBool (hdi ==~ i1) (lift hdt) $ resolveEnv tl i1

movementTypeCheck :: TypingEnv -> UnionM MovingExpr -> ExceptT MovingError UnionM MovingType
movementTypeCheck env e = do
  et <- typeCheckU env e
  merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch

-- typeCheckOld :: TypingEnv -> MovingExpr -> ExceptT MovingError UnionM MovingType
-- typeCheckOld _ (Coord (CoordLit _ _)) = mrgReturn CoordType
-- typeCheckOld _ (Coord UnitLit) = mrgReturn UnitType
-- typeCheckOld env (Moving (MoveUp e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheckOld env (Moving (MoveDown e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheckOld env (Moving (MoveLeft e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheckOld env (Moving (MoveRight e)) = do
--   et <- typeCheckU env e
--   merge $ if et == CoordType then return CoordType else throwError $ MovingTyper TypeMismatch
-- typeCheckOld env (MovingVarExpr i) = resolveEnv env i
--   where
--     resolveEnv [] _ = merge $ throwError $ MovingTyper MovingTypeVarNotFound
--     resolveEnv ((hdi, hdt) : tl) i1 = mrgIf @SymBool (hdi ==~ i1) (lift hdt) $ resolveEnv tl i1

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
interpret _ (Coord c) = lift c >>= return
interpret env (Moving e) = do
  concMove <- mrgLift e
  interpretMovement env concMove
interpret env (MovingVarExpr i) = reduceValue env i

interpretMovement :: ExecutingEnv -> MovingOpExpr -> ExceptT MovingError UnionM CoordExpr
interpretMovement env (MoveUp e) = do
  ev <- interpretU env e
  reduceMoveUp ev
interpretMovement env (MoveDown e) = do
  ev <- interpretU env e
  reduceMoveDown ev
interpretMovement env (MoveLeft e) = do
  ev <- interpretU env e
  reduceMoveLeft ev
interpretMovement env (MoveRight e) = do
  ev <- interpretU env e
  reduceMoveRight ev


-- interpret env (Moving (MoveUp e)) = do
--   ev <- interpretU env e
--   reduceMoveUp ev
-- interpret env (Moving (MoveDown e)) = do
--   ev <- interpretU env e
--   reduceMoveDown ev
-- interpret env (Moving (MoveLeft e)) = do
--   ev <- interpretU env e
--   reduceMoveLeft ev
-- interpret env (Moving (MoveRight e)) = do
--   ev <- interpretU env e
--   reduceMoveRight ev
-- interpret env (MovingVarExpr i) = reduceValue env i

-- typeCheck env (Coord coord) = do
--   concCoord <- lift coord
--   case concCoord of
--     UnitLit -> mrgReturn UnitType
--     (CoordLit _ _) -> mrgReturn CoordType
-- typeCheck env (Moving e) = do
--   concMove <- lift e
--   case concMove of 
--     (MoveUp e) -> movementTypeCheck env e
--     (MoveDown e) -> movementTypeCheck env e
--     (MoveLeft e) -> movementTypeCheck env e
--     (MoveRight e) -> movementTypeCheck env e
-- typeCheck env (MovingVarExpr i) = resolveEnv env i



-- interpretOld :: ExecutingEnv -> MovingExpr -> ExceptT MovingError UnionM CoordExpr
-- interpretOld _ (Coord c) = mrgReturn c
-- interpretOld env (Moving (MoveUp e)) = do
--   ev <- interpretU env e
--   reduceMoveUp ev
-- interpretOld env (Moving (MoveDown e)) = do
--   ev <- interpretU env e
--   reduceMoveDown ev
-- interpretOld env (Moving (MoveLeft e)) = do
--   ev <- interpretU env e
--   reduceMoveLeft ev
-- interpretOld env (Moving (MoveRight e)) = do
--   ev <- interpretU env e
--   reduceMoveRight ev
-- interpretOld env (MovingVarExpr i) = reduceValue env i

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


{-

• Overlapping instances for ToCon
                              (UnionMBase SymBool MovingExpr)
                              (UnionMBase SymBool ConcMovingExpr)
    arising from the 'deriving' clause of a data type declaration
  Matching instances:
    instance (SymBoolOp bool, ToCon a b) => ToCon (UnionMBase bool a) b
      
      -- Defined in ‘Grisette.Control.Monad.UnionMBase’
    
    instance (SymBoolOp bool, ToCon a b, Mergeable bool b) =>
              ToCon (UnionMBase bool a) (UnionMBase bool b)
      
      -- Defined in ‘Grisette.Control.Monad.UnionMBase’


-}