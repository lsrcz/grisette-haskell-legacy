{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Denotation where

import Data.Bifunctor
import qualified Data.ByteString as B
import Data.HashMap.Strict as M
import Evaluator
import Grisette
import Grisette.Unordered.UUnionM
import Language.Haskell.TH.Syntax.Compat
import Syntax
import Table

moveQuotesOut :: [SpliceQ e] -> SpliceQ [e]
moveQuotesOut [] = [||[]||]
moveQuotesOut (x : xs) = [||$$x : $$(moveQuotesOut xs)||]

denoteSql :: Query -> SpliceQ Table
denoteSql (QueryNamed n) = liftSplice $ fail $ "There are unresolved tables " ++ show n
denoteSql (QueryTable t) = [||t||]
denoteSql (QueryJoin q1 q2) =
  [||xproduct $$(denoteSql q1) $$(denoteSql q2) "dummy"||]
denoteSql (QueryLeftOuterJoin q1 q2 i1 i2) =
  [||leftOuterJoin $$(denoteSql q1) $$(denoteSql q2) i1 i2||]
denoteSql (QueryLeftOuterJoin2 q1 q2 q12) =
  [||leftOuterJoin2 $$(denoteSql q1) $$(denoteSql q2) $$(denoteSql q12)||]
denoteSql (QueryRename q nm) = [||renameTable nm $$(denoteSql q)||]
denoteSql (QueryRenameFull q nm scheme) =
  [||renameTableFull nm scheme $$(denoteSql q)||]
denoteSql (QueryUnionAll q1 q2) =
  [||unionAll $$(denoteSql q1) $$(denoteSql q2)||]
denoteSql qs@(QuerySelect cols q f) =
  let schema = extractSchema q
      indexMap = Prelude.foldr (\(i, n) b -> M.insert n i b) M.empty (zip [0 ..] schema)
      queryQ = denoteSql q
      filterQ = denoteFilter f indexMap
      rowFuncs = moveQuotesOut $ (\arg -> denoteValue (ValColumnRef arg) indexMap) <$> cols
      newSchema = extractSchema qs
      newTblName = "dummy"
   in [||
      let rowFuncs1 = $$rowFuncs
          rowFuncWrap r = (\rf -> rf r) <$> rowFuncs1
          fromContent = case $$queryQ of
            Table _ _ c -> c
          postFilter = (\(r, p) -> (r, mrgIte @SymBool ($$filterQ r) p 0)) <$> fromContent
          content = first rowFuncWrap <$> postFilter
       in Table newTblName newSchema content
      ||]
denoteSql q = liftSplice $ fail $ "I don't know how to handle the sql query " ++ show q

denoteFilter :: Filter -> M.HashMap Table.Name Int -> SpliceQ ([UUnionM (Maybe SymInteger)] -> SymBool)
denoteFilter FilterTrue _ = [||const $ conc True||]
denoteFilter FilterFalse _ = [||const $ conc False||]
denoteFilter (FilterNot f) indexMap = [||nots . $$(denoteFilter f indexMap)||]
denoteFilter (FilterConj f1 f2) indexMap =
  [||\e -> $$(denoteFilter f1 indexMap) e &&~ $$(denoteFilter f2 indexMap) e||]
denoteFilter (FilterDisj f1 f2) indexMap =
  [||\e -> $$(denoteFilter f1 indexMap) e ||~ $$(denoteFilter f2 indexMap) e||]
denoteFilter (FilterBinOp FBinEq v1 v2) indexMap =
  [||\e -> $$(denoteValue v1 indexMap) e ==~ $$(denoteValue v2 indexMap) e||]
denoteFilter (FilterBinOp FBinNEq v1 v2) indexMap =
  [||\e -> $$(denoteValue v1 indexMap) e /=~ $$(denoteValue v2 indexMap) e||]

-- denoteFilter f _ = fail $ "I don't know how to handle the sql filter " ++ show f

denoteValue ::
  Val ->
  M.HashMap Table.Name Int ->
  SpliceQ ([UUnionM (Maybe SymInteger)] -> UUnionM (Maybe SymInteger))
denoteValue (ValConst i) _ = [||const $ mrgReturn i||]
denoteValue (ValColumnRef s) indexMap =
  case M.lookup s indexMap of
    Just i -> [||(!! i)||]
    Nothing -> liftSplice $ fail $ "Unknown column " ++ show s ++ " referenced in the context " ++ show indexMap

extractSchema :: Query -> Schema
extractSchema (QueryNamed n) = fail $ "There are unresolved tables " ++ show n
extractSchema (QueryTable t) = tableQualifiedSchema t
extractSchema (QueryJoin q1 q2) =
  extractSchema q1 ++ extractSchema q2
extractSchema (QueryRenameFull _ nm schema) =
  fmap (B.append (B.append nm ".")) schema
extractSchema (QuerySelect cols _ _) =
  fmap (const "dummy") cols
extractSchema q = fail $ "I don't know how to extract schema for the query " ++ show q
