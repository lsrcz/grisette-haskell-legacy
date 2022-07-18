{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import GHC.Generics
import Data.Proxy
import Grisette

data Coord = Coord SymInteger SymInteger
  deriving (Show, Generic, GenSym SymBool ())
  deriving (Mergeable SymBool) via (Default Coord)

data Move
  = ExactCoord Coord
  | MoveLeft (UnionM Move)
  | MoveRight (UnionM Move)
  deriving (Show, Generic)
  deriving (Mergeable SymBool) via (Default Move)

instance GenSymSimple (Sym Bool) () Coord where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

$(makeUnionMWrapper "u" ''Move)

instance GenSym (Sym Bool) (Int, Coord) Move where
  genSymFresh (v, coord) =
    if v <= 0
      then do
        return $ uExactCoord coord
      else do
        m <- genSymFresh (v - 1, coord)
        choose [ExactCoord coord, MoveLeft m, MoveRight m]

instance GenSym (Sym Bool) Int (Coord -> UnionM Move) where

instance GenSymSimple (Sym Bool) Int (Coord -> UnionM Move) where
  genSymSimpleFresh proxy v =
    if v <= 0
      then do
        return uExactCoord 
      else do
        m <- genSymSimpleFresh proxy (v - 1)
        simpleChoose proxy [uExactCoord, uMoveLeft . m, uMoveRight . m]

-- The following should lie in Grisette lib
extractArgFromListOfFunc :: [a -> b] -> a -> [b]
extractArgFromListOfFunc l a = (\x -> x a) <$> l

extractArgFromUnionMBaseOfFunc :: (SymBoolOp bool, Mergeable bool b) => UnionMBase bool (a -> b) -> a -> UnionMBase bool b
extractArgFromUnionMBaseOfFunc l a = mrgFmap (\x -> x a) l

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec (a -> b), Mergeable bool b) =>
  GenSym bool (ListSpec spec) (a -> UnionMBase bool [b])
  where

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec (a -> b), Mergeable bool b) =>
  GenSymSimple bool (ListSpec spec) (a -> UnionMBase bool [b])
  where
  genSymSimpleFresh _ spec = do
    l <- genSymFresh spec
    return $ extractArgFromUnionMBaseOfFunc (extractArgFromListOfFunc <$> l)

-- The previous section should lie in Grisette lib

genSketch :: ListSpec Int -> GenSymIdent -> Coord -> UnionM [UnionM Move]
genSketch (ListSpec minl maxl sub) nm coord = genSym (ListSpec minl maxl (sub, coord)) nm

genSketchBetter :: ListSpec Int -> GenSymIdent -> Coord -> UnionM [UnionM Move]
genSketchBetter (ListSpec minl maxl sub) = genSymSimple (Proxy :: Proxy SymBool) (ListSpec minl maxl sub)

sketch :: Coord -> UnionM [UnionM Move]
sketch = genSketch (ListSpec 0 1 1) "a"

sketch1 :: Coord -> UnionM [UnionM Move]
sketch1 = genSketchBetter (ListSpec 0 1 1) "a"

main :: IO ()
main = do
  print $ sketch (Coord (conc 0) (conc 0))
  print $ sketch (genSymSimple (Proxy :: Proxy SymBool) () "coord")
  print $ sketch1 (Coord (conc 0) (conc 0))
  print $ sketch1 (genSymSimple (Proxy :: Proxy SymBool) () "coord")
