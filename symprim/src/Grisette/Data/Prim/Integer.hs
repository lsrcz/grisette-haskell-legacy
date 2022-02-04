{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.Integer
  ( integerConcTermView,
    pattern IntegerConcTerm,
    pattern IntegerTerm,
    DivI (..),
    divi,
    pattern DivITerm,
    ModI (..),
    modi,
    pattern ModITerm,
  )
where

import Control.DeepSeq
import Data.Typeable
import GHC.Generics
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm
import Language.Haskell.TH.Syntax

integerConcTermView :: forall a. Term a -> Maybe Integer
integerConcTermView (ConcTerm _ b) = cast b
integerConcTermView _ = Nothing

pattern IntegerConcTerm :: Integer -> Term a
pattern IntegerConcTerm b <- (integerConcTermView -> Just b)

integerTermView :: Term a -> Maybe (Term Integer)
integerTermView = castTerm

pattern IntegerTerm :: Term Integer -> Term a
pattern IntegerTerm b <- (integerTermView -> Just b)

-- div
data DivI = DivI deriving (Show, Lift, Generic, NFData)

divi :: Term Integer -> Term Integer -> Term Integer
divi = partialEvalBinary DivI

instance BinaryPartialStrategy DivI Integer Integer Integer where
  extractora _ = integerConcTermView
  extractorb _ = integerConcTermView
  allConstantHandler _ i j
    | j /= 0 = Just $ concTerm $ i `div` j
  allConstantHandler _ _ _ = Nothing
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ i 1 = Just i
  rightConstantHandler _ _ _ = Nothing
  nonBinaryConstantHandler _ _ _ = Nothing

instance BinaryOp DivI Integer Integer Integer where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial @DivI tag) (constructBinary tag) l r
  pformatBinary _ l r = "(/I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern DivITerm :: Term Integer -> Term Integer -> Term a
pattern DivITerm l r <- BinaryTermPatt DivI l r

-- mod
data ModI = ModI deriving (Show, Lift, Generic, NFData)

modi :: Term Integer -> Term Integer -> Term Integer
modi = partialEvalBinary ModI

instance BinaryPartialStrategy ModI Integer Integer Integer where
  extractora _ = integerConcTermView
  extractorb _ = integerConcTermView
  allConstantHandler _ i j
    | j /= 0 = Just $ concTerm $ i `mod` j
  allConstantHandler _ _ _ = Nothing
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ i 1 = Just i
  rightConstantHandler _ _ _ = Nothing
  nonBinaryConstantHandler _ _ _ = Nothing

instance BinaryOp ModI Integer Integer Integer where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(%I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern ModITerm :: Term Integer -> Term Integer -> Term a
pattern ModITerm l r <- BinaryTermPatt ModI l r
