{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
module Main where
import Grisette.Data.SymPrim
import Grisette.Control.Monad.UnionM
import GHC.Generics
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper (conc)

data Coord = Coord SymInteger SymInteger deriving (Show, Generic)

data Move
  = ExactCoord Coord
  | MoveLeft (UnionM Move)
  | MoveRight (UnionM Move)
  deriving (Show, Generic)

instance Mergeable (Sym Bool) Coord where

instance SymGen (Sym Bool) () Coord where
  genSymIndexed v = genSymSimpleIndexed @SymBool v

instance SymGenSimple (Sym Bool) () Coord where
  genSymSimpleIndexed _ = do
    x <- genSymSimpleIndexed @SymBool ()
    y <- genSymSimpleIndexed @SymBool ()
    return $ Coord x y

instance Mergeable (Sym Bool) Move where
instance SymGen (Sym Bool) (Int, Coord) Move where
  genSymIndexed (v, coord) = if v <= 0 then do
    return $ mrgSingle $ ExactCoord coord
    else do
    m <- genSymIndexed @SymBool (v - 1, coord)
    choose (ExactCoord coord) [MoveLeft m, MoveRight m]

genSketch :: ListSpec Int -> String -> Coord -> UnionM [UnionM Move]
genSketch (ListSpec minl maxl sub) name coord = genSym (ListSpec minl maxl (sub, coord)) name

sketch :: Coord -> UnionM [UnionM Move]
sketch = genSketch (ListSpec 0 1 1) "a"

main :: IO ()
main = do
  print $ sketch (Coord (conc 0) (conc 0))
  print $ sketch (genSymSimple @SymBool () "coord")


