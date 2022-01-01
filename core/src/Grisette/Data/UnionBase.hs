{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Grisette.Data.UnionBase (UnionBase (..)) where

import Data.Functor.Classes
import Grisette.Data.Class.Bool
import Grisette.Data.Class.UnionOp
import Data.Hashable
import GHC.Generics

data UnionBase b a
  = Single a
  | Guard a b (UnionBase b a) (UnionBase b a)
  deriving (Show, Generic, Eq)

instance SymBoolOp bool => UnionOp bool (UnionBase bool) where
  single = Single
  guard cond ifTrue ifFalse = Guard (leftMost ifTrue) cond ifTrue ifFalse
  singleView (Single a) = Just a
  singleView _ = Nothing
  guardView (Guard _ cond ifTrue ifFalse) = Just (cond, ifTrue, ifFalse)
  guardView _ = Nothing
  leftMost (Single a) = a
  leftMost (Guard a _ _ _) = a

instance (Show b) => Show1 (UnionBase b) where
  liftShowsPrec sp _ i (Single a) s =
    "Single(" ++ sp i a ")" ++ s
  liftShowsPrec sp sl i (Guard _ cond t f) s =
    "Guard(" ++ showsPrec i cond (liftShowsPrec sp sl i t (liftShowsPrec sp sl i f ")")) ++ s

instance (Hashable b, Hashable a) => Hashable (UnionBase b a) where
  s `hashWithSalt` (Single a) = s `hashWithSalt` (0 :: Int) `hashWithSalt` a
  s `hashWithSalt` (Guard _ c l r) = s `hashWithSalt` (1 :: Int) `hashWithSalt` c `hashWithSalt` l `hashWithSalt` r
