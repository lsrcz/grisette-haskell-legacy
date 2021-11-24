{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Grisette.Data.TabularFunc (type (=->) (..)) where

import Data.Hashable
import GHC.Generics
import Grisette.Data.Class.FiniteFunction

data (=->) a b = TabularFunc {funcTable :: [(a, b)], defaultFuncValue :: b} deriving (Show, Eq, Generic)

infixr 0 =->

instance (Eq a) => FiniteFunction (a =-> b) a b where
  runFunc (TabularFunc table defaultValue) a = go table
    where
      go [] = defaultValue
      go ((av, bv) : s)
        | a == av = bv
        | otherwise = go s

instance (Hashable a, Hashable b) => Hashable (a =-> b)
