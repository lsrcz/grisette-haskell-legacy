{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.TabularFunc
  ( pattern TabularFuncConcTerm,
    pattern TabularFuncTerm,
    ApplyF (..),
    applyf,
    pattern ApplyFTerm,
  )
where

import Control.DeepSeq
import Data.Data
import GHC.Generics
import Grisette.Data.Class.Function
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.TabularFunc
import Language.Haskell.TH.Syntax

tabularFuncConcTermView :: forall a b c. (Typeable b, Typeable c) => Term a -> Maybe (b =-> c)
tabularFuncConcTermView (ConcTerm _ b) = cast b
tabularFuncConcTermView _ = Nothing

pattern TabularFuncConcTerm :: (Typeable b, Typeable c) => (b =-> c) -> Term a
pattern TabularFuncConcTerm b <- (tabularFuncConcTermView -> Just b)

tabularFuncTermView :: forall a b c. (Typeable b, Typeable c) => Term a -> Maybe (Term (b =-> c))
tabularFuncTermView = castTerm

pattern TabularFuncTerm :: (Typeable b, Typeable c) => Term (b =-> c) -> Term a
pattern TabularFuncTerm b <- (tabularFuncTermView -> Just b)

-- apply
data ApplyF = ApplyF deriving (Show, Lift, Generic, NFData)

instance (Show a, Show b, SupportedPrim a, SupportedPrim b) => BinaryPartialStrategy ApplyF (a =-> b) a b where
  extractora _ = tabularFuncConcTermView
  extractorb _ = \case
    (ConcTerm _ b) -> cast b
    _ -> Nothing
  allConstantHandler _ f a = Just $ concTerm $ f # a
  leftConstantHandler _ (TabularFunc f d) a = Just $ go f
    where
      go [] = concTerm d
      go ((x, y) : xs) = iteterm (eqterm a (concTerm x)) (concTerm y) (go xs)
  rightConstantHandler _ _ _ = Nothing
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Show a, Show b, SupportedPrim a, SupportedPrim b) => BinaryOp ApplyF (a =-> b) a b where
  partialEvalBinary tag l r = totalize2 (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(" ++ pformat l ++ " " ++ pformat r ++ ")"

applyf :: (Show a, Show b, SupportedPrim a, SupportedPrim b) => Term (a =-> b) -> Term a -> Term b
applyf = partialEvalBinary ApplyF

pattern ApplyFTerm :: (Typeable a, Typeable b) => Term (a =-> b) -> Term a -> Term b
pattern ApplyFTerm l r <- BinaryTermPatt ApplyF l r