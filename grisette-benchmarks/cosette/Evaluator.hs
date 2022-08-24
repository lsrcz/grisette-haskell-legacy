module Evaluator where

import Data.Bifunctor
import qualified Data.ByteString as B
import Grisette
import Table

xproduct :: Table -> Table -> Name -> Table
xproduct a@(Table _ _ ca) b@(Table _ _ cb) nm =
  Table
    nm
    (schemaJoin a b)
    (merge $ xproductRaw <$> ca <*> cb)

xproductRaw :: RawTable -> RawTable -> RawTable
xproductRaw x y = (\((l1, n1), (l2, n2)) -> (l1 ++ l2, n1 * n2)) <$> cartesProd x y

cartesProd :: forall a b. [a] -> [b] -> [(a, b)]
cartesProd a b = [(x, y) | x <- a, y <- b]

equiJoin :: RawTable -> RawTable -> [(Int, Int)] -> Int -> RawTable
equiJoin content1 content2 indexPairs schemaSize1 =
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
    $ xproductRaw content1 content2

unionAll :: Table -> Table -> Table
unionAll (Table n1 s1 c1) (Table _ _ c2) = Table n1 s1 (unionAllRawU c1 c2)

unionAllRawU :: UnionM RawTable -> UnionM RawTable -> UnionM RawTable
unionAllRawU x1 x2 = do
  x1r <- x1
  x2r <- x2
  mrgReturn $ unionAllRaw x1r x2r

unionAllRaw :: RawTable -> RawTable -> RawTable
unionAllRaw = (++)

leftOuterJoin :: Table -> Table -> Int -> Int -> Table
leftOuterJoin t1@(Table n1 s1 c1) t2@(Table n2 s2 c2) index1 index2 =
  Table
    (B.append n1 n2)
    (schemaJoin t1 t2)
    $ do
      c1v <- c1
      c2v <- c2
      leftOuterJoinRaw c1v c2v index1 index2 (length s1) (length s2)

leftOuterJoin2 :: Table -> Table -> Table -> Table
leftOuterJoin2 t1@(Table n1 s1 c1) t2@(Table n2 s2 _) (Table _ _ c12) =
  Table
    (B.append n1 n2)
    (schemaJoin t1 t2)
    $ do
      c1v <- c1
      c12v <- c12
      addingNullRows c1v c12v (length s1) (length s2)

leftOuterJoinRaw :: RawTable -> RawTable -> Int -> Int -> Int -> Int -> UnionM RawTable
leftOuterJoinRaw content1 content2 index1 index2 schemaSize1 =
  addingNullRows content1 (equiJoin content1 content2 [(index1, index2)] schemaSize1) schemaSize1

dedup :: RawTable -> UnionM RawTable
dedup [] = mrgReturn []
dedup ((ele, mult) : xs) = mrgIf (mult ==~ 0) (dedup xs) $ do
  f <- symFilter (\(ele1, _) -> nots $ ele ==~ ele1) xs
  d <- dedup f
  return $ (ele, 1) : d

dedupAccum :: RawTable -> UnionM RawTable
dedupAccum [] = mrgReturn []
dedupAccum l@((ele, _) : xs) = do
  fl <- yl
  fntl <- ntl
  mrgReturn $ (ele, sum $ snd <$> fl) : fntl
  where
    yl = symFilter (\(ele1, _) -> ele ==~ ele1) l
    ntl = do
      f <- symFilter (\(ele1, _) -> nots $ ele ==~ ele1) xs
      dedupAccum f

tableDiff :: RawTable -> RawTable -> UnionM RawTable
tableDiff tbl1 tbl2 = do
  t1v <- t1
  mrgReturn $ cal <$> t1v
  where
    t1 = dedupAccum tbl1
    cal (ele, mult) =
      let rowCount = getRowCount ele tbl2
          mult1 = mult - rowCount
          multr = mrgIte @SymBool (mult1 >~ 0) mult1 0
       in (ele, multr)

getRowCount :: [UnionM (Maybe SymInteger)] -> RawTable -> SymInteger
getRowCount row tbl = sum $ (\(ele, mult) -> mrgIte @SymBool (ele ==~ row) mult 0) <$> tbl

addingNullRows :: RawTable -> RawTable -> Int -> Int -> UnionM RawTable
addingNullRows content1 content12 schemaSize1 schemaSize2 = do
  er <- extraRows
  mrgReturn $ unionAllRaw content12 ((\(ele, mult) -> (ele ++ nullCols, mult)) <$> er)
  where
    nullCols :: [UnionM (Maybe SymInteger)]
    nullCols = [mrgReturn Nothing | _ <- [0 .. schemaSize2 - 1]]
    diffKeys :: UnionM RawTable
    diffKeys = do
      d1 <- dedup content1
      let p12 = projection [0 .. schemaSize1 - 1] content12
      d12 <- dedup p12
      td <- tableDiff d1 d12
      dedup td
    extraRows :: UnionM RawTable
    extraRows = do
      dk <- diffKeys
      mrgReturn $
        projection [0 .. schemaSize1 - 1] $
          equiJoin content1 dk [(x, x) | x <- [0 .. schemaSize1 - 1]] schemaSize1

projection :: [Int] -> RawTable -> RawTable
projection indices = fmap (first projSingle)
  where
    projSingle r = fmap (r !!) indices
