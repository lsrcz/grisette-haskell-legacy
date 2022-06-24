{-# LANGUAGE OverloadedStrings #-}

module Table where

import qualified Data.ByteString as B
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Instances.TH.Lift ()
import qualified Language.Haskell.TH.Syntax as THSyntax

type Name = B.ByteString

type Schema = [Name]

type RawTable = [([UnionM (Maybe SymInteger)], SymInteger)]

data Table = Table
  { tableName :: Name,
    tableSchema :: Schema,
    tableContent :: UnionM RawTable
  }
  deriving (Show, THSyntax.Lift, Generic, SymEval Model)

instance Mergeable SymBool Table where
  mergingStrategy = SimpleStrategy $ mrgIte @SymBool

instance SimpleMergeable SymBool Table where
  mrgIte cond (Table name1 schema1 content1) (Table name2 schema2 content2)
    | name1 /= name2 || schema1 /= schema2 = error "Bad merge"
    | otherwise = Table name1 schema1 $ mrgIf cond content1 content2

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
tableRepOk (Table _ _ c) = getSingle $ do
  c1 <- c
  mrgReturn $ foldr (\(_, p) a -> a &&~ p >=~ 0) (conc True) c1
