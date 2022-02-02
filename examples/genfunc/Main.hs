{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term

data Coord = Coord SymInteger SymInteger
  deriving (Show, Generic, Mergeable SymBool, SymGen SymBool ())

data Move
  = ExactCoord Coord
  | MoveLeft (UnionM Move)
  | MoveRight (UnionM Move)
  deriving (Show, Generic, Mergeable SymBool)

instance SymGenSimple (Sym Bool) () Coord where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @SymBool

$(makeUnionMWrapper "u" ''Move)

instance SymGen (Sym Bool) (Int, Coord) Move where
  genSymIndexed (v, coord) =
    if v <= 0
      then do
        return $ uExactCoord coord
      else do
        m <- genSymIndexed @SymBool (v - 1, coord)
        choose (ExactCoord coord) [MoveLeft m, MoveRight m]

instance SymGen (Sym Bool) Int (Coord -> UnionM Move) where

instance SymGenSimple (Sym Bool) Int (Coord -> UnionM Move) where
  genSymSimpleIndexed v =
    if v <= 0
      then do
        return uExactCoord 
      else do
        m <- genSymSimpleIndexed @SymBool (v - 1)
        simpleChoose @SymBool uExactCoord [uMoveLeft . m, uMoveRight . m]

-- The following should lie in Grisette lib
extractArgFromListOfFunc :: [a -> b] -> a -> [b]
extractArgFromListOfFunc l a = (\x -> x a) <$> l

extractArgFromUnionMBaseOfFunc :: (SymBoolOp bool, Mergeable bool b) => UnionMBase bool (a -> b) -> a -> UnionMBase bool b
extractArgFromUnionMBaseOfFunc l a = mrgFmap (\x -> x a) l

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec (a -> b), Mergeable bool b) =>
  SymGen bool (ListSpec spec) (a -> UnionMBase bool [b])
  where

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec (a -> b), Mergeable bool b) =>
  SymGenSimple bool (ListSpec spec) (a -> UnionMBase bool [b])
  where
  genSymSimpleIndexed spec = do
    l <- genSymIndexed @bool @(ListSpec spec) @[a -> b] spec
    return $ extractArgFromUnionMBaseOfFunc (extractArgFromListOfFunc <$> l)

-- The previous section should lie in Grisette lib

genSketch :: ListSpec Int -> String -> Coord -> UnionM [UnionM Move]
genSketch (ListSpec minl maxl sub) name coord = genSym (ListSpec minl maxl (sub, coord)) name

genSketchBetter :: ListSpec Int -> String -> Coord -> UnionM [UnionM Move]
genSketchBetter (ListSpec minl maxl sub) = genSymSimple @SymBool (ListSpec minl maxl sub)

sketch :: Coord -> UnionM [UnionM Move]
sketch = genSketch (ListSpec 0 1 1) "a"

sketch1 :: Coord -> UnionM [UnionM Move]
sketch1 = genSketchBetter (ListSpec 0 1 1) "a"

main :: IO ()
main = do
  print $ sketch (Coord (conc 0) (conc 0))
  print $ sketch (genSymSimple @SymBool () "coord")
  print $ sketch1 (Coord (conc 0) (conc 0))
  print $ sketch1 (genSymSimple @SymBool () "coord")
