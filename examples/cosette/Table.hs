{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Table where

import qualified Data.ByteString as B
import Grisette.Data.SymPrim
import qualified Language.Haskell.TH.Syntax as THSyntax
import Instances.TH.Lift ()
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SymEval
import GHC.Generics
import Grisette.Data.Prim.Model

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
renameTableFull name schema t =
  if length schema /= length (tableSchema t)
    then error "Bad cols"
    else t {tableName = name, tableSchema = schema}

tableQualifiedSchema :: Table -> Schema
tableQualifiedSchema t = fmap (B.append (B.append (tableName t) ".")) (tableSchema t)

renameCols :: Table -> Schema -> Table
renameCols t cols =
  if length cols /= length (tableSchema t)
    then error "Bad cols"
    else t {tableSchema = cols}

schemaJoin :: Table -> Table -> Schema
schemaJoin (Table n1 s1 _) (Table n2 s2 _) =
  renamed1 ++ renamed2
  where
    renamed1 = fmap (B.append (B.append n1 "+")) s1
    renamed2 = fmap (B.append (B.append n2 "+")) s2

tableRepOk :: Table -> SymBool
tableRepOk (Table _ _ c) = foldr (\(_, p) a -> a &&~ p >=~ 0) (conc True) c
