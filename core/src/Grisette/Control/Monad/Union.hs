{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Grisette.Control.Monad.Union where
import Grisette.Control.Monad.Union.UnionOp
import Grisette.Data.Class.Bool

data UnionBase b a
  = Single a
  | Guard a b (UnionBase b a) (UnionBase b a)
  deriving Show

instance SymBoolOp bool => UnionOp bool (UnionBase bool) where
  single = Single
  guard cond ifTrue ifFalse = Guard (leftMost ifTrue) cond ifTrue ifFalse
  singleView (Single a) = Just a
  singleView _ = Nothing
  guardView (Guard _ cond ifTrue ifFalse) = Just (cond, ifTrue, ifFalse)
  guardView _ = Nothing
  leftMost (Single a) = a
  leftMost (Guard a _ _ _) = a

