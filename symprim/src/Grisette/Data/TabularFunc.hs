{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Data.TabularFunc (type (=->) (..)) where

import Data.Hashable
import GHC.Generics
import Grisette.Data.Class.FiniteFunction
import Grisette.Data.Prim.InternedTerm

data (=->) a b = TabularFunc {funcTable :: [(a, b)], defaultFuncValue :: b} deriving (Show, Eq, Generic)

infixr 0 =->

instance
  (SupportedPrim a, SupportedPrim b) =>
  SupportedPrim (a =-> b) where
    defaultValue = TabularFunc [] (defaultValue @b)


instance (Eq a) => FiniteFunction (a =-> b) where
  type Arg (a =-> b) = a
  type Ret (a =-> b) = b
  runFunc (TabularFunc table d) a = go table
    where
      go [] = d
      go ((av, bv) : s)
        | a == av = bv
        | otherwise = go s

instance (Hashable a, Hashable b) => Hashable (a =-> b)
