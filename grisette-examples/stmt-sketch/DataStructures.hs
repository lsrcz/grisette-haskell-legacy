{-# LANGUAGE TemplateHaskell #-}
module DataStructures where

import Data.List (intercalate)
import Generics.Deriving
import Grisette
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
  deriving (Eq, Generic)
  deriving (ToCon SymbExpr) via (Default ConcExpr)

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
      Lift
    )
  deriving
    ( SEq SymBool,
      Mergeable SymBool,
      Evaluate Model,
      ToSym ConcExpr
    ) via (Default SymbExpr)

newtype Identifier = Identifier Integer
  deriving (Eq, Generic)
  deriving (ToCon SIdentifier) via (Default Identifier)

newtype SIdentifier = SIdentifier SymInteger
  deriving
    ( Show,
      Eq,
      Generic,
      Lift
    )
  deriving
    ( SEq SymBool,
      Mergeable SymBool,
      SimpleMergeable SymBool,
      Evaluate Model,
      ToSym Identifier
    ) via (Default SIdentifier)

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

instance GenSym SymBool () SIdentifier where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance GenSymSimple SymBool () SIdentifier where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @SymBool

instance GenSym SymBool [Integer] SIdentifier

instance GenSymSimple SymBool [Integer] SIdentifier where
  genSymSimpleFresh l = simpleChoose @SymBool (SIdentifier . conc <$> l)

data Stmt
  = AssignStmt Identifier ConcExpr
  | IfStmt ConcExpr [Stmt] [Stmt]
  | AssertStmt ConcExpr
  deriving (Eq, Generic)
  deriving (ToCon SymbStmt) via (Default Stmt)

data SymbStmt
  = SAssignStmt SIdentifier (UnionM SymbExpr)
  | SIfStmt (UnionM SymbExpr) [SymbStmt] [SymbStmt]
  | SAssertStmt (UnionM SymbExpr)
  deriving
    ( Show,
      Eq,
      Generic,
      Lift
    )
  deriving
    ( SEq SymBool,
      Mergeable SymBool,
      Evaluate Model,
      ToSym Stmt
    ) via (Default SymbStmt)

newtype Program = Program [Stmt]
  deriving (Eq, Generic)
  deriving (ToCon SymbProgram) via (Default Program)

newtype SymbProgram = SymbProgram [SymbStmt]
  deriving
    ( Show,
      Eq,
      Generic,
      Lift
    )
  deriving
    ( SEq SymBool,
      Mergeable SymBool,
      Evaluate Model,
      ToSym Program
    ) via (Default SymbProgram)

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
