{-# LANGUAGE OverloadedStrings #-}

module Table where

import qualified Data.ByteString as B
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Instances.TH.Lift ()
import qualified Language.Haskell.TH.Syntax as THSyntax
import Data.Bifunctor

type Name = B.ByteString

type Schema = [Name]

type UnderlyingTable = [([UnionM (Maybe SymInteger)], SymInteger)]
newtype RawTable = RawTable { underlyingTable :: UnderlyingTable }
  deriving (Show, THSyntax.Lift, Generic, SymEval Model)

instance Mergeable SymBool RawTable where

instance SimpleMergeable SymBool RawTable where
  mrgIte cond (RawTable tb1) (RawTable tb2) =
    RawTable $ (second (\m -> mrgIte cond m 0) <$> tb1) ++ (second (mrgIte cond 0) <$> tb2)

data Table = Table
  { tableName :: Name,
    tableSchema :: Schema,
    tableContent :: RawTable
  }
  deriving (Show, THSyntax.Lift, Generic, SymEval Model)

instance Mergeable SymBool Table where
  mergeStrategy = SimpleStrategy $ mrgIte @SymBool

instance SimpleMergeable SymBool Table where
  mrgIte cond (Table name1 schema1 content1) (Table name2 schema2 content2)
    | name1 /= name2 || schema1 /= schema2 = error "Bad merge"
    | otherwise = Table name1 schema1 $ mrgIte cond content1 content2

renameTable :: Name -> Table -> Table
renameTable name t = t {tableName = name}

renameTableFull :: Name -> Schema -> Table -> Table
renameTableFull name schema t
  | length schema /= length (tableSchema t) = error "Bad cols"
  | otherwise = t {tableName = name, tableSchema = schema}

tableQualifiedSchema :: Table -> Schema
tableQualifiedSchema t = fmap (B.append (B.append (tableName t) ".")) (tableSchema t)

renameCols :: Table -> Schema -> Table
renameCols t cols
  | length cols /= length (tableSchema t) = error "Bad cols"
  | otherwise = t {tableSchema = cols}

schemaJoin :: Table -> Table -> Schema
schemaJoin (Table n1 s1 _) (Table n2 s2 _) =
  (B.append (B.append n1 "+") <$> s1) ++ (B.append (B.append n2 "+") <$> s2)

tableRepOk :: Table -> SymBool
tableRepOk (Table _ _ (RawTable c)) = foldr (\(_, p) a -> a &&~ p >=~ 0) (conc True) c
