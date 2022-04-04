{-# LANGUAGE TemplateHaskell #-}

module Value where

import Control.DeepSeq
import Generics.Deriving
import Grisette.Core
import Grisette.SymPrim.Term

data PCValue = PCValue {int :: SymInteger, label :: SymBool}
  deriving (Show, Eq, Generic, Mergeable SymBool, SymEval Model)
  deriving (SimpleMergeable SymBool, NFData)
  deriving (SEq SymBool) via (Default PCValue)

$(makeUnionMWrapper "u" ''PCValue)

instance SymGen SymBool () PCValue

instance SymGenSimple SymBool () PCValue where
  genSymSimpleIndexed () = genSymSimpleIndexedWithDerivedNoSpec @SymBool

instance SymGen SymBool PCValue PCValue

instance SymGenSimple SymBool PCValue PCValue where
  genSymSimpleIndexed i = genSymIndexedWithDerivedSameShape @SymBool i

zeroLow :: PCValue
zeroLow = PCValue 0 $ conc False

data MemValue
  = MPCValue PCValue
  | ReturnAddr PCValue PCValue
  deriving (Show, Eq, Generic, Mergeable SymBool, SymEval Model, NFData)
  deriving (SEq SymBool) via (Default MemValue)
