{-# LANGUAGE TemplateHaskell #-}
module Expr where

import GHC.Generics
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term

data ConcExpr
  = ConstantExpr Integer
  | AddExpr ConcExpr ConcExpr
  | SubExpr ConcExpr ConcExpr
  | MulExpr ConcExpr ConcExpr
  deriving (Show, Eq, Generic, ToCon SymbExpr)

data SymbExpr
  = SConstantExpr SymInteger
  | SAddExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SSubExpr (UnionM SymbExpr) (UnionM SymbExpr)
  | SMulExpr (UnionM SymbExpr) (UnionM SymbExpr)
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool, SymEval Model, ToSym ConcExpr)

$(makeUnionMWrapper "u" ''SymbExpr)

interpret :: SymbExpr -> SymInteger
interpret (SConstantExpr s) = s
interpret (SAddExpr a b) = interpret #~ a + interpret #~ b
interpret (SSubExpr a b) = interpret #~ a - interpret #~ b
interpret (SMulExpr a b) = interpret #~ a * interpret #~ b

synthesis :: GrisetteSMTConfig i -> UnionM SymbExpr -> Integer -> IO (Maybe ConcExpr)
synthesis config s i = do
  m <- solveWith config (interpret #~ s ==~ toSym i)
  case m of
    Left _ -> return Nothing
    Right mo -> return $ toCon $ symeval True mo s
