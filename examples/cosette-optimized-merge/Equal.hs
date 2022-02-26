{-# LANGUAGE TemplateHaskell #-}

module Equal where

import Denotation
import Grisette.Core
import Grisette.SymPrim.Term
import Language.Haskell.TH
import Syntax
import Table

getMultiplicity :: [UnionM (Maybe SymInteger)] -> RawTable -> SymInteger
getMultiplicity r (RawTable ut) = foldr (\(r1, p1) t -> mrgIte @SymBool (r1 ==~ r) p1 0 + t) 0 ut

tableSum :: RawTable -> RawTable
tableSum rt@(RawTable t) = RawTable $ (\(r, _) -> (r, getMultiplicity r rt)) <$> t

elementContain :: ([UnionM (Maybe SymInteger)], SymInteger) -> RawTable -> SymBool
elementContain r@(_, p) (RawTable t) = (p ==~ 0) ||~ foldr (\r1 a -> a ||~ r ==~ r1) (conc False) t

contain :: RawTable -> RawTable -> SymBool
contain (RawTable t1) t2 = foldr (\r a -> a &&~ elementContain r t2) (conc True) t1

bagEqual :: RawTable -> RawTable -> SymBool
bagEqual t1 t2 =
  let l1 = tableSum t1
      l2 = tableSum t2
   in contain l1 l2 &&~ contain l2 l1

same :: Query -> Query -> Q (TExp SymBool)
same q1 q2 = [||bagEqual (tableContent $$(denoteSql q1)) (tableContent $$(denoteSql q2))||]

tableAllRepOk :: Query -> Q (TExp SymBool)
tableAllRepOk (QueryTable t) = [||tableRepOk t||]
tableAllRepOk (QueryJoin q1 q2) = [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2)||]
tableAllRepOk (QueryLeftOuterJoin2 q1 q2 q12) =
  [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2) &&~ $$(tableAllRepOk q12)||]
tableAllRepOk (QueryRename q _) = [||$$(tableAllRepOk q)||]
tableAllRepOk (QueryRenameFull q _ _) = [||$$(tableAllRepOk q)||]
tableAllRepOk (QuerySelect _ q _) = [||$$(tableAllRepOk q)||]
tableAllRepOk (QueryNamed n) = fail $ "There are unresolved tables " ++ show n
tableAllRepOk q = fail $ "Don't know how to determine rep ok for " ++ show q

verifCondition :: Query -> Query -> Q (TExp SymBool)
verifCondition q1 q2 = [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2) &&~ (nots $$(same q1 q2))||]
