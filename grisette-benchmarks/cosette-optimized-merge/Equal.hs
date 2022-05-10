{-# LANGUAGE TemplateHaskell #-}

module Equal where

import Denotation
import Grisette
import Language.Haskell.TH.Syntax.Compat
import Syntax
import Table

getMultiplicity :: [UnionM (Maybe SymInteger)] -> RawTable -> SymInteger
getMultiplicity r = foldr (\(r1, p1) t -> mrgIte @SymBool (r1 ==~ r) p1 0 + t) 0

tableSum :: RawTable -> RawTable
tableSum t = (\(r, _) -> (r, getMultiplicity r t)) <$> t

elementContain :: ([UnionM (Maybe SymInteger)], SymInteger) -> RawTable -> SymBool
elementContain r = foldr (\r1 a -> a ||~ r ==~ r1) (conc False)

contain :: RawTable -> RawTable -> SymBool
contain t1 t2 = foldr (\r a -> a &&~ elementContain r t2) (conc True) t1

bagEqual :: RawTable -> RawTable -> SymBool
bagEqual t1 t2 =
  let l1 = tableSum t1
      l2 = tableSum t2
   in contain l1 l2 &&~ contain l2 l1

same :: Query -> Query -> SpliceQ SymBool
same q1 q2 = [||bagEqual (tableContent $$(denoteSql q1)) (tableContent $$(denoteSql q2))||]

tableAllRepOk :: Query -> SpliceQ SymBool
tableAllRepOk (QueryTable t) = [||tableRepOk t||]
tableAllRepOk (QueryJoin q1 q2) = [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2)||]
tableAllRepOk (QueryLeftOuterJoin q1 q2 _ _) =
  [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2)||]
tableAllRepOk (QueryLeftOuterJoin2 q1 q2 q12) =
  [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2) &&~ $$(tableAllRepOk q12)||]
tableAllRepOk (QueryRename q _) = [||$$(tableAllRepOk q)||]
tableAllRepOk (QueryRenameFull q _ _) = [||$$(tableAllRepOk q)||]
tableAllRepOk (QuerySelect _ q _) = [||$$(tableAllRepOk q)||]
tableAllRepOk (QueryNamed n) = liftSplice $ fail $ "There are unresolved tables " ++ show n
tableAllRepOk q = liftSplice $ fail $ "Don't know how to determine rep ok for " ++ show q

verifCondition :: Query -> Query -> SpliceQ SymBool
verifCondition q1 q2 = [||$$(tableAllRepOk q1) &&~ $$(tableAllRepOk q2) &&~ (nots $$(same q1 q2))||]
