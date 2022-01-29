{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveAnyClass #-}

module Grisette.Data.TabularFunc (type (=->) (..)) where

import Data.Hashable
import GHC.Generics
import Grisette.Data.Class.FiniteFunction
import Grisette.Data.Prim.InternedTerm
import Language.Haskell.TH.Syntax
import Control.DeepSeq

data (=->) a b = TabularFunc {funcTable :: [(a, b)], defaultFuncValue :: b} deriving (Show, Eq, Generic, Generic1, Lift, NFData, NFData1)

infixr 0 =->

instance
  (SupportedPrim a, SupportedPrim b) =>
  SupportedPrim (a =-> b)
  where
  type PrimConstraint (a =-> b) = (SupportedPrim a, SupportedPrim b)
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
