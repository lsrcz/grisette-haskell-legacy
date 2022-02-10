{-# LANGUAGE TemplateHaskell #-}
module Value where

import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Control.DeepSeq

data PCValue = PCValue {int :: SymInteger, label :: SymBool}
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool, SymEval Model)
  deriving (SimpleMergeable SymBool, NFData)

$(makeUnionMWrapper "u" ''PCValue)

instance SymGen SymBool () PCValue 

instance SymGenSimple SymBool () PCValue where
  genSymSimpleIndexed () = genSymSimpleIndexedWithDerivedNoSpec @SymBool

instance SymGen SymBool PCValue PCValue where

instance SymGenSimple SymBool PCValue PCValue where
  genSymSimpleIndexed i = genSymIndexedWithDerivedSameShape @SymBool i

zeroLow :: PCValue
zeroLow = PCValue 0 $ conc False

data MemValue
  = MPCValue PCValue
  | ReturnAddr PCValue PCValue
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool, SymEval Model, NFData)
