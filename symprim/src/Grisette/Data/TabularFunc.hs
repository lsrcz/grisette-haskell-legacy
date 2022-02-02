module Grisette.Data.TabularFunc
  ( type (=->) (..),
  )
where

import Control.DeepSeq
import Data.Hashable
import GHC.Generics
import Grisette.Data.Class.Function
import Grisette.Data.Prim.InternedTerm
import Language.Haskell.TH.Syntax

data (=->) a b = TabularFunc {funcTable :: [(a, b)], defaultFuncValue :: b} deriving (Show, Eq, Generic, Generic1, Lift, NFData, NFData1)

infixr 0 =->

instance
  (SupportedPrim a, SupportedPrim b) =>
  SupportedPrim (a =-> b)
  where
  type PrimConstraint (a =-> b) = (SupportedPrim a, SupportedPrim b)
  defaultValue = TabularFunc [] (defaultValue @b)

instance (Eq a) => Function (a =-> b) where
  type Arg (a =-> b) = a
  type Ret (a =-> b) = b
  (TabularFunc table d) # a = go table
    where
      go [] = d
      go ((av, bv) : s)
        | a == av = bv
        | otherwise = go s

instance (Hashable a, Hashable b) => Hashable (a =-> b)
