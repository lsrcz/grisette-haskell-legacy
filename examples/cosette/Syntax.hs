{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax where

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Grisette.Data.SymPrim
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Table

data FBinOp = FBinEq | FBinNEq deriving (Show, Lift)

data Val
  = ValConst (Maybe SymInteger)
  | ValColumnRef B.ByteString
  deriving (Show, Lift)

data Query
  = QuerySelect [B.ByteString] Query Filter
  | QuerySelectDistinct [B.ByteString] Query Filter
  | QueryJoin Query Query
  | QueryNamed B.ByteString
  | QueryTable Table
  | QueryRename Query B.ByteString
  | QueryRenameFull Query B.ByteString [B.ByteString]
  | QueryLeftOuterJoin2 Query Query Query
  | QueryUnionAll Query Query
  | QuerySub B.ByteString
  deriving (Show)

apply :: Language.Haskell.TH.Name -> [Q Exp] -> Q Exp
apply n = foldl appE (conE n)

instance Lift Query where
  lift (QuerySelect l q f) = [|QuerySelect l q f|]
  lift (QuerySelectDistinct l q f) = [|QuerySelectDistinct l q f|]
  lift (QueryJoin q1 q2) = [|QueryJoin q1 q2|]
  lift (QueryNamed n) = apply 'QueryTable [varE $ mkName $ C.unpack n] --[|QueryNamed n|]
  lift (QueryTable n) = [|QueryTable n|]
  lift (QueryRename q n) = [|QueryRename q n|]
  lift (QueryRenameFull q n s) = [|QueryRenameFull q n s|]
  lift (QueryLeftOuterJoin2 q1 q2 q3) = [|QueryLeftOuterJoin2 q1 q2 q3|]
  lift (QueryUnionAll q1 q2) = [|QueryUnionAll q1 q2|]
  lift (QuerySub s) = varE $ mkName $ C.unpack s
  liftTyped = unsafeTExpCoerce . lift

data Filter
  = FilterBinOp FBinOp Val Val
  | FilterConj Filter Filter
  | FilterDisj Filter Filter
  | FilterNot Filter
  | FilterExists Query
  | FilterTrue
  | FilterFalse
  deriving (Show, Lift)