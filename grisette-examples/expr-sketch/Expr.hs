{-# LANGUAGE TemplateHaskell #-}

module Expr where

import Generics.Deriving
import Grisette

data ConcExpr
  = ConstantExpr Integer
  | AddExpr ConcExpr ConcExpr
  | SubExpr ConcExpr ConcExpr
  | MulExpr ConcExpr ConcExpr
  deriving (Show, Eq, Generic)
  deriving (ToCon SymbExpr) via (Default ConcExpr)

data SymbExpr
  = SConstantExpr SymInteger
  | SAddExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SSubExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SMulExpr (UnionM SymbExpr) (UnionM SymbExpr)
  deriving (Show, Eq, Generic)
  deriving (SEq SymBool, Mergeable SymBool, Evaluate Model, ToSym ConcExpr) via (Default SymbExpr)

$(makeUnionMWrapper "u" ''SymbExpr)

interpret :: SymbExpr -> SymInteger
interpret (SConstantExpr s) = s
interpret (SAddExpr a b) = interpret #~ a + interpret #~ b
interpret (SSubExpr a b) = interpret #~ a - interpret #~ b
interpret (SMulExpr a b) = interpret #~ a * interpret #~ b

synthesis :: GrisetteSMTConfig i -> UnionM SymbExpr -> Integer -> IO (Maybe ConcExpr)
synthesis config s i = do
  m <- solveFormula config (interpret #~ s ==~ toSym i)
  case m of
    Left _ -> return Nothing
    Right mo -> return $ toCon $ evaluate True mo s
