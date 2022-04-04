{-# LANGUAGE TemplateHaskell #-}
module DataStructures where

import Data.List (intercalate)
import Generics.Deriving
import Grisette.Core
import Grisette.SymPrim.Term
import Language.Haskell.TH.Syntax (Lift)

data ConcExpr
  = IntConstantExpr Integer
  | BoolConstantExpr Bool
  | VarExpr Identifier
  | LtExpr ConcExpr ConcExpr
  | EqExpr ConcExpr ConcExpr
  | AndExpr ConcExpr ConcExpr
  | OrExpr ConcExpr ConcExpr
  | AddExpr ConcExpr ConcExpr
  | SubExpr ConcExpr ConcExpr
  | MulExpr ConcExpr ConcExpr
  deriving (Eq, Generic, ToCon SymbExpr)

data SymbExpr
  = SIntConstantExpr SymInteger
  | SBoolConstantExpr SymBool
  | SVarExpr SIdentifier
  | SLtExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SEqExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SAndExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SOrExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SAddExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SSubExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SMulExpr (UnionM SymbExpr) (UnionM SymbExpr)
  deriving
    ( Show,
      Eq,
      Generic,
      Mergeable SymBool,
      SymEval Model,
      ToSym ConcExpr,
      Lift
    )
  deriving (SEq SymBool) via (Default SymbExpr)

newtype Identifier = Identifier Integer
  deriving (Eq, Generic, ToCon SIdentifier)

newtype SIdentifier = SIdentifier SymInteger
  deriving
    ( Show,
      Eq,
      Generic,
      Mergeable SymBool,
      SimpleMergeable SymBool,
      SymEval Model,
      ToSym Identifier,
      Lift
    )
  deriving (SEq SymBool) via (Default SIdentifier)

$(makeUnionMWrapper "u" ''SymbExpr)
$(makeUnionMWrapper "u" ''SIdentifier)

addParen :: String -> String
addParen s = "(" ++ s ++ ")"

addParenPrio :: Int -> Int -> String -> String
addParenPrio i j s = if i <= j then addParen s else s

showOp :: Int -> Int -> String -> ConcExpr -> ConcExpr -> String
showOp i j op l r = addParenPrio i j $ showExpr (i - 1) l ++ " " ++ op ++ " " ++ showExpr i r

showExpr :: Int -> ConcExpr -> String
showExpr _ (IntConstantExpr i) = show i
showExpr _ (BoolConstantExpr b) = show b
showExpr _ (VarExpr b) = show b
showExpr i (OrExpr l r) = showOp 0 i "||" l r
showExpr i (AndExpr l r) = showOp 1 i "&&" l r
showExpr i (EqExpr l r) = showOp 2 i "==" l r
showExpr i (LtExpr l r) = showOp 2 i "<" l r
showExpr i (AddExpr l r) = showOp 3 i "+" l r
showExpr i (SubExpr l r) = showOp 3 i "-" l r
showExpr i (MulExpr l r) = showOp 4 i "*" l r

instance Show ConcExpr where
  show = showExpr 10

instance Show Identifier where
  show (Identifier i) = "v" ++ show i

instance SymGen SymBool () SIdentifier where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

instance SymGenSimple SymBool () SIdentifier where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @SymBool

instance SymGen SymBool [Integer] SIdentifier

instance SymGenSimple SymBool [Integer] SIdentifier where
  genSymSimpleIndexed l =
    let l1 = SIdentifier . conc <$> l
     in simpleChoose @SymBool (head l1) (tail l1)

data Stmt
  = AssignStmt Identifier ConcExpr
  | IfStmt ConcExpr [Stmt] [Stmt]
  | AssertStmt ConcExpr
  deriving (Eq, Generic, ToCon SymbStmt)

data SymbStmt
  = SAssignStmt SIdentifier (UnionM SymbExpr)
  | SIfStmt (UnionM SymbExpr) [SymbStmt] [SymbStmt]
  | SAssertStmt (UnionM SymbExpr)
  deriving
    ( Show,
      Eq,
      Generic,
      Mergeable SymBool,
      SymEval Model,
      ToSym Stmt,
      Lift
    )
  deriving (SEq SymBool) via (Default SymbStmt)

newtype Program = Program [Stmt] deriving (Eq, Generic, ToCon SymbProgram)

newtype SymbProgram = SymbProgram [SymbStmt]
  deriving
    ( Show,
      Eq,
      Generic,
      Mergeable SymBool,
      SymEval Model,
      ToSym Program,
      Lift
    )
  deriving (SEq SymBool) via (Default SymbProgram)

instance Show Stmt where
  show (AssertStmt e) = "assert " ++ show e
  show (AssignStmt i e) = show i ++ " = " ++ show e
  show (IfStmt cond l r) =
    "if (" ++ show cond ++ ") {\n"
      ++ unlines (showStmtIdent 1 <$> l)
      ++ "} else {\n"
      ++ unlines (showStmtIdent 1 <$> r)
      ++ "}"

showStmtIdent :: Int -> Stmt -> String
showStmtIdent i s = intercalate "\n" $ (\x -> concat (replicate i "  ") ++ x) <$> lines (show s)

instance Show Program where
  show (Program l) = unlines $ show <$> l
