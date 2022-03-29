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
    tableContent :: RawTable
  }
  deriving (Show, THSyntax.Lift, Generic, SymEval Model)

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
tableRepOk (Table _ _ c) = foldr (\(_, p) a -> a &&~ p >=~ 0) (conc True) c