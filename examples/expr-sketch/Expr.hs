module Expr where

import Data.List (sort)
import Data.List.Unique
import GHC.Generics
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Prim.Model
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.SymPrim

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

data Op = Add | Sub | Mul deriving (Show, Eq, Ord)

instance SymGen SymBool [Op] (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr) where
  genSymIndexed s = mrgSingle <$> genSymSimpleIndexed @SymBool s

instance SymGenSimple SymBool [Op] (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr) where
  genSymSimpleIndexed s = getSingle <$> choose @SymBool (head ops) (tail ops)
    where
      ops =
        (\op x y -> mrgSingle $ op x y)
          . ( \case
                Add -> SAddExpr
                Sub -> SSubExpr
                Mul -> SMulExpr
            )
          <$> uniq (sort s)

interpretU :: UnionM SymbExpr -> SymInteger
interpretU u = getSingle $ interpret <$> u

interpret :: SymbExpr -> SymInteger
interpret (SConstantExpr s) = s
interpret (SAddExpr a b) = interpretU a + interpretU b
interpret (SSubExpr a b) = interpretU a - interpretU b
interpret (SMulExpr a b) = interpretU a * interpretU b

synthesis :: GrisetteSMTConfig i -> UnionM SymbExpr -> Integer -> IO (Maybe ConcExpr)
synthesis config s i = do
  m <- solveWith config (interpretU s ==~ toSym i)
  case m of
    Left _ -> return Nothing
    Right mo -> return $ toCon $ symeval True mo s
