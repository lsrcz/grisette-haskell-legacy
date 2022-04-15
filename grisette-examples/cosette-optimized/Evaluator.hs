module Evaluator where

import Data.Bifunctor
import qualified Data.ByteString as B
import Grisette.Core
import Grisette.SymPrim.Term
import Table

xproduct :: Table -> Table -> Name -> Table
xproduct a@(Table _ _ ca) b@(Table _ _ cb) name = Table name (schemaJoin a b) (xproductRaw ca cb)

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
unionAll (Table n1 s1 c1) (Table _ _ c2) = Table n1 s1 (unionAllRaw c1 c2)

unionAllRaw :: RawTable -> RawTable -> RawTable
unionAllRaw = (++)

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
leftOuterJoinRaw content1 content2 index1 index2 schemaSize1 =
  addingNullRows content1 (equiJoin content1 content2 [(index1, index2)] schemaSize1) schemaSize1

addingNullRows :: RawTable -> RawTable -> Int -> Int -> RawTable
addingNullRows content1 content12 schemaSize1 schemaSize2 =
  unionAllRaw content12 (fmap (first (++ nullCols)) diffKeys)
  where
    nullCols :: [UnionM (Maybe SymInteger)]
    nullCols = [mrgReturn Nothing | _ <- [0 .. schemaSize2 -1]]
    diffKeys = removeSameKeys content1 (fmap (first (take schemaSize1)) content12)

projection :: [Int] -> RawTable -> RawTable
projection indices = fmap (first projSingle)
  where
    projSingle r = fmap (r !!) indices

removeSameKeys :: RawTable -> RawTable -> RawTable
removeSameKeys t1 t2 =
  foldr
    ( \(v, p) acc ->
        let multiplicity = mrgIte @SymBool (foldr (||~) (conc False) $ fmap (\(v1, r1) -> v ==~ v1 &&~ r1 /=~ 0) t2) 0 p
         in if multiplicity == 0 {- using == here is intentional -} then acc else (v, multiplicity) : acc
    )
    []
    t1
