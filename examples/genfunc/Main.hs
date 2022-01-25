{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import GHC.Generics
import Grisette.Control.Monad.UnionM
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper (conc)
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.UnionOp
import Grisette.Data.SymPrim
import Grisette.Data.Functor

data Coord = Coord SymInteger SymInteger deriving (Show, Generic)

data Move
  = ExactCoord Coord
  | MoveLeft (UnionM Move)
  | MoveRight (UnionM Move)
  deriving (Show, Generic)

instance Mergeable (Sym Bool) Coord

instance SymGen (Sym Bool) () Coord where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple (Sym Bool) () Coord where
  genSymSimpleIndexed _ = do
    x <- genSymSimpleIndexed @SymBool ()
    y <- genSymSimpleIndexed @SymBool ()
    return $ Coord x y

instance Mergeable (Sym Bool) Move

instance SymGen (Sym Bool) (Int, Coord) Move where
  genSymIndexed (v, coord) =
    if v <= 0
      then do
        return $ mrgSingle $ ExactCoord coord
      else do
        m <- genSymIndexed @SymBool (v - 1, coord)
        choose (ExactCoord coord) [MoveLeft m, MoveRight m]

instance SymGen (Sym Bool) Int (Coord -> UnionM Move) where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple (Sym Bool) Int (Coord -> UnionM Move) where
  genSymSimpleIndexed v =
    if v <= 0
      then do
        return $ \coord -> mrgSingle $ ExactCoord coord
      else do
        m <- genSymSimpleIndexed @SymBool (v - 1)
        r <- choose (mrgSingle . ExactCoord) [mrgSingle . MoveLeft . m, mrgSingle . MoveRight . m]
        return $ getSingle @SymBool r

-- The following should lie in Grisette lib
extractArgFromListOfFunc :: [a -> b] -> a -> [b]
extractArgFromListOfFunc l a = (\x -> x a) <$> l

extractArgFromUnionMBaseOfFunc :: (SymBoolOp bool, Mergeable bool b) => UnionMBase bool (a -> b) -> a -> UnionMBase bool b
extractArgFromUnionMBaseOfFunc l a = mrgFmap (\x -> x a) l

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec (a -> b), Mergeable bool b) =>
  SymGen bool (ListSpec spec) (a -> UnionMBase bool [b]) where
  genSymIndexed v = genSymSimpleIndexed @bool v

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
  print ()
  print ()
  print $ sketch (Coord (conc 0) (conc 0))
  print $ sketch (genSymSimple @SymBool () "coord")
  print $ sketch1 (Coord (conc 0) (conc 0))
  print $ sketch1 (genSymSimple @SymBool () "coord")