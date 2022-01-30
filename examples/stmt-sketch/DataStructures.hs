module DataStructures where

import Data.List (intercalate, sort)
import Data.List.Unique
import GHC.Generics
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
      SEq SymBool,
      SymEval Model,
      ToSym ConcExpr,
      Lift
    )

data Op = Add | Sub | Mul | Lt | Eq | And | Or deriving (Show, Eq, Ord)

instance SymGen SymBool [Op] (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)

instance SymGenSimple SymBool [Op] (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr) where
  genSymSimpleIndexed s = simpleChoose @SymBool (head ops) (tail ops)
    where
      ops =
        (\op x y -> mrgSingle $ op x y)
          . ( \case
                Add -> SAddExpr
                Sub -> SSubExpr
                Mul -> SMulExpr
                Lt -> SLtExpr
                Eq -> SEqExpr
                And -> SAndExpr
                Or -> SOrExpr
            )
          <$> uniq (sort s)

newtype Identifier = Identifier Integer
  deriving (Eq, Generic, ToCon SIdentifier)

instance Show Identifier where
  show (Identifier i) = "v" ++ show i

newtype SIdentifier = SIdentifier SymInteger
  deriving
    ( Show,
      Eq,
      Generic,
      Mergeable SymBool,
      SimpleMergeable SymBool,
      SEq SymBool,
      SymEval Model,
      ToSym Identifier,
      Lift
    )

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
      SEq SymBool,
      SymEval Model,
      ToSym Stmt,
      Lift
    )

newtype Program = Program [Stmt] deriving (Eq, Generic, ToCon SymbProgram)

newtype SymbProgram = SymbProgram [SymbStmt]
  deriving
    ( Show,
      Eq,
      Generic,
      Mergeable SymBool,
      SEq SymBool,
      SymEval Model,
      ToSym Program,
      Lift
    )

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
