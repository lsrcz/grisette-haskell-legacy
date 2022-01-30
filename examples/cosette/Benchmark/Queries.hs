{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Benchmark.Queries where

import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Quasiquote
import Syntax
import Table

symt :: Table
symt = Table "t" ["tid", "name"]
  [(mrgSingle . Just <$> [ssymb "t0-0", ssymb "t0-1"], ssymb "t0-p")]
symtr :: Table
symtr = Table "tr" ["rid", "tid", "name"]
  [(mrgSingle . Just <$> [ssymb "tr0-0", ssymb "tr0-1", ssymb "tr0-2"], ssymb "tr0-p")]
symta :: Table
symta = Table "ta" ["rid", "status"]
  [(mrgSingle . Just <$> [ssymb "ta0-0", ssymb "ta0-1"], ssymb "ta0-p")]
symtb :: Table
symtb = Table "tb" ["rid", "status"]
  [(mrgSingle . Just <$> [ssymb "tb0-0", ssymb "tb0-1"], ssymb "tb0-p")]

conct :: Table
conct = Table "t" ["tid", "name"]
  [(mrgSingle . Just <$> [-8, 0], 3)]
conctr :: Table
conctr = Table "tr" ["rid", "tid", "name"]
  [(mrgSingle . Just <$> [-8, -8, 2], 0)]
concta :: Table
concta = Table "ta" ["rid", "status"]
  [(mrgSingle . Just <$> [-3, 0], 0)]
conctb :: Table
conctb = Table "tb" ["rid", "status"]
  [(mrgSingle . Just <$> [-8, 0], 0)]

t :: Table
t = symt
tr :: Table
tr = symtr
ta :: Table
ta = symta
tb :: Table
tb = symtb

q1 :: Query
q1 = [cosette|
  AS (LEFT-OUTER-JOIN2
  (NAMED t)
  (NAMED tr)
  (SELECT t0.tid1 t0.name t0.rid t0.tid2 t0.type
   FROM (AS (JOIN (NAMED t) (NAMED tr)) t0 [tid1, name, rid, tid2, type])
   WHERE t0.tid1 = t0.tid2))
  t1 [tid1, name, rid, tid2, type]
  |]

q1r :: Query
q1r = [cosette|
  SELECT t0.tid1 t0.name t0.rid t0.tid2 t0.type
  FROM (AS (JOIN (NAMED t) (NAMED tr)) t0 [tid1, name, rid, tid2, type])
  WHERE t0.tid1 = t0.tid2
  |]

q2 :: Query
q2 = [cosette|
  LEFT-OUTER-JOIN2
  (${q1})
  (NAMED ta)
  (SELECT t0.tid1 t0.name t0.rid t0.tid2 t0.type t0.rid2 t0.status1
   FROM (AS (JOIN (${q1}) (NAMED ta)) t0 [tid1, name, rid, tid2, type, rid2, status1])
   WHERE t0.type = 1 AND t0.rid = t0.rid2)|]

q2r :: Query
q2r = [cosette|
  LEFT-OUTER-JOIN2
  (${q1r})
  (NAMED ta)
  (SELECT t0.tid1 t0.name t0.rid t0.tid2 t0.type t0.rid2 t0.status1
   FROM (AS (JOIN (${q1r}) (NAMED ta)) t0 [tid1, name, rid, tid2, type, rid2, status1])
   WHERE t0.rid <> NULL AND t0.type = 1 AND t0.rid = t0.rid2)|]

q3 :: Query
q3 = [cosette|
  AS (LEFT-OUTER-JOIN2
  (${q2})
  (NAMED tb)
  (SELECT t0.tid1 t0.name t0.rid t0.tid2 t0.type t0.rid2 t0.status1 t0.rid3 t0.status2
   FROM (AS (JOIN (${q2}) (NAMED tb)) t0 [tid1, name, rid, tid2, type, rid2, status1, rid3, status2])
   WHERE t0.type = 2 AND t0.rid = t0.rid3))
  t0 [tid1, name, rid, tid2, type, rid2, status1, rid3, status2]|]

q3r :: Query
q3r = [cosette|
  AS (LEFT-OUTER-JOIN2
  (${q2r})
  (NAMED tb)
  (SELECT t0.tid1 t0.name t0.rid t0.tid2 t0.type t0.rid2 t0.status1 t0.rid3 t0.status2
   FROM (AS (JOIN (${q2r}) (NAMED tb)) t0 [tid1, name, rid, tid2, type, rid2, status1, rid3, status2])
   WHERE t0.rid <> NULL AND t0.type = 2 AND t0.rid = t0.rid3))
  t0 [tid1, name, rid, tid2, type, rid2, status1, rid3, status2]|]

q4 :: Query
q4 = [cosette|
  SELECT t0.tid1 t0.name t0.status1 t0.status2
  FROM (${q3})
  WHERE TRUE|]

q4r :: Query
q4r = [cosette|
  SELECT t0.tid1 t0.name t0.status1 t0.status2
  FROM (${q3r})
  WHERE TRUE|]
