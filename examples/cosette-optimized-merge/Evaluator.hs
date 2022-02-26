module Evaluator where

import Data.Bifunctor
import qualified Data.ByteString as B
import Grisette.Core
import Grisette.SymPrim.Term
import Table

xproduct :: Table -> Table -> Name -> Table
xproduct a@(Table _ _ ca) b@(Table _ _ cb) name = Table name (schemaJoin a b) (xproductRaw ca cb)

xproductRaw :: RawTable -> RawTable -> RawTable
xproductRaw (RawTable x) (RawTable y) = RawTable $ xproductRaw' x y
xproductRaw' :: UnderlyingTable -> UnderlyingTable -> UnderlyingTable
xproductRaw' x y = (\((l1, n1), (l2, n2)) -> (l1 ++ l2, n1 * n2)) <$> cartesProd x y

cartesProd :: forall a b. [a] -> [b] -> [(a, b)]
cartesProd a b = [(x, y) | x <- a, y <- b]

equiJoin' :: UnderlyingTable -> UnderlyingTable -> [(Int, Int)] -> Int -> UnderlyingTable
equiJoin' content1 content2 indexPairs schemaSize1 =
  foldr
    ( \(v, p) acc ->
        let multiplicity =
              mrgIte @SymBool
                ( foldr (&&~) (conc True) $
                    fmap (\(i1, i2) -> v !! i1 ==~ v !! (i2 + schemaSize1)) indexPairs
                )
                p
                0
         in if multiplicity == 0 then acc else (v, multiplicity) : acc
    )
    []
    $ xproductRaw' content1 content2

unionAll :: Table -> Table -> Table
unionAll (Table n1 s1 c1) (Table _ _ c2) = Table n1 s1 (unionAllRaw c1 c2)

unionAllRaw :: RawTable -> RawTable -> RawTable
unionAllRaw (RawTable l) (RawTable r) = RawTable $ unionAllRaw' l r

unionAllRaw' :: UnderlyingTable -> UnderlyingTable -> UnderlyingTable
unionAllRaw' l r = l ++ r

leftOuterJoin :: Table -> Table -> Int -> Int -> Table
leftOuterJoin t1@(Table n1 s1 c1) t2@(Table n2 s2 c2) index1 index2 =
  Table
    (B.append n1 n2)
    (schemaJoin t1 t2)
    (leftOuterJoinRaw c1 c2 index1 index2 (length s1) (length s2))

leftOuterJoin2 :: Table -> Table -> Table -> Table
leftOuterJoin2 t1@(Table n1 s1 c1) t2@(Table n2 s2 _) (Table _ _ c12) =
  Table
    (B.append n1 n2)
    (schemaJoin t1 t2)
    (addingNullRows c1 c12 (length s1) (length s2))

leftOuterJoinRaw :: RawTable -> RawTable -> Int -> Int -> Int -> Int -> RawTable
leftOuterJoinRaw (RawTable c1) (RawTable c2) index1 index2 schemaSize1 v = RawTable $ 
  leftOuterJoinRaw' c1 c2 index1 index2 schemaSize1 v

leftOuterJoinRaw' :: UnderlyingTable -> UnderlyingTable -> Int -> Int -> Int -> Int -> UnderlyingTable
leftOuterJoinRaw' content1 content2 index1 index2 schemaSize1 =
  addingNullRows' content1 (equiJoin' content1 content2 [(index1, index2)] schemaSize1) schemaSize1

filter0 :: UnderlyingTable -> UnderlyingTable
filter0 = filter (\(_, n) -> n /= 0) 

dedup :: RawTable -> RawTable
dedup (RawTable r) = RawTable $ dedup' r
dedup' :: UnderlyingTable -> UnderlyingTable
dedup' [] = []
dedup' ((ele, mult) : xs) = underlyingTable $ mrgIte (mult ==~ 0 :: SymBool) (RawTable $ dedup' xs) $
  let
    f = (\(ele1, m) -> (ele1, mrgIte (ele ==~ ele1 :: SymBool) 0 m)) <$> xs
    d = dedup' f
   in RawTable $ (ele, 1) : d

dedupAccum :: RawTable -> RawTable
dedupAccum = undefined
dedupAccum' :: UnderlyingTable -> UnderlyingTable
dedupAccum' [] = []
dedupAccum' l@((ele, _) : xs) =
  (ele, sum $ snd <$> yl) : ntl
  where
    yl = filter0 $ (\(ele1, m) -> (ele1, mrgIte (ele ==~ ele1:: SymBool) m 0)) <$> l
    ntl = dedupAccum' $ filter0 $ (\(ele1, m) -> (ele1, mrgIte (ele ==~ ele1:: SymBool) 0 m)) <$> xs

tableDiff' :: UnderlyingTable -> UnderlyingTable -> UnderlyingTable
tableDiff' tbl1 tbl2 = filter0 $ cal <$> t1
  where
    t1 = dedupAccum' tbl1
    cal (ele, mult) =
      let rowCount = getRowCount' ele tbl2
          mult1 = mult - rowCount
          multr = mrgIte @SymBool (mult1 >~ 0) mult1 0
       in (ele, multr)

getRowCount' :: [UnionM (Maybe SymInteger)] -> UnderlyingTable -> SymInteger
getRowCount' row tbl = sum $ (\(ele, mult) -> mrgIte @SymBool (ele ==~ row) mult 0) <$> tbl

addingNullRows :: RawTable -> RawTable -> Int -> Int -> RawTable
addingNullRows (RawTable content1) (RawTable content12) schemaSize1 schemaSize2 = RawTable $
  addingNullRows' content1 content12 schemaSize1 schemaSize2

addingNullRows' :: UnderlyingTable -> UnderlyingTable -> Int -> Int -> UnderlyingTable
addingNullRows' content1 content12 schemaSize1 schemaSize2 =
  unionAllRaw' content12 ((\(ele, mult) -> (ele ++ nullCols, mult)) <$> extraRows)
  where
    nullCols :: [UnionM (Maybe SymInteger)]
    nullCols = [mrgReturn Nothing | _ <- [0 .. schemaSize2 -1]]
    diffKeys :: UnderlyingTable
    diffKeys = 
      let
        d1 = dedup' content1
        pl2 = projection' [0 .. schemaSize1 - 1] content12
        d12 = dedup' pl2
        td = tableDiff' d1 d12
        in dedup' td
    extraRows :: UnderlyingTable
    extraRows = 
      projection' [0 .. schemaSize1 -1] $
        equiJoin' content1 diffKeys [(x, x) | x <- [0 .. schemaSize1 -1]] schemaSize1

projection' :: [Int] -> UnderlyingTable -> UnderlyingTable
projection' indices = fmap (first projSingle)
  where
    projSingle r = fmap (r !!) indices
