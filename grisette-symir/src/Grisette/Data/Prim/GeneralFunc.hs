{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Grisette.Data.Prim.GeneralFunc where

import Language.Haskell.TH.Syntax
import GHC.Generics
import Control.DeepSeq
import Data.Hashable
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Helpers
import Grisette.Data.GeneralFunc
import Data.Typeable
import Grisette.Core.Data.Class.Function

generalFuncConcTermView :: forall a b c. (Typeable b, Typeable c) => Term a -> Maybe (b --> c)
generalFuncConcTermView (ConcTerm _ b) = cast b
generalFuncConcTermView _ = Nothing

pattern GeneralFuncConcTerm :: (Typeable b, Typeable c) => (b --> c) -> Term a
pattern GeneralFuncConcTerm b <- (generalFuncConcTermView -> Just b)

generalFuncTermView :: forall a b c. (Typeable b, Typeable c) => Term a -> Maybe (Term (b --> c))
generalFuncTermView = castTerm

pattern GeneralFuncTerm :: (Typeable b, Typeable c) => Term (b --> c) -> Term a
pattern GeneralFuncTerm b <- (generalFuncTermView -> Just b)

data ApplyG = ApplyG deriving (Show, Lift, Generic, NFData, Eq, Hashable)

instance (SupportedPrim a, SupportedPrim b) => BinaryPartialStrategy ApplyG (a --> b) a b where
  extractora _ = \case
    (ConcTerm _ b) -> cast b
    _ -> Nothing
  extractorb _ = \case
    (ConcTerm _ b) -> cast b
    _ -> Nothing
  allConstantHandler _ f a = Just $ f # concTerm a
  leftConstantHandler _ f a = Just $ f # a
  rightConstantHandler _ _ _ = Nothing
  nonBinaryConstantHandler _ _ _ = Nothing

instance (SupportedPrim a, SupportedPrim b) => BinaryOp ApplyG (a --> b) a b where
  partialEvalBinary tag l r = totalize2 (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(" ++ pformat l ++ " " ++ pformat r ++ ")"

applyg :: (SupportedPrim a, SupportedPrim b) => Term (a --> b) -> Term a -> Term b
applyg = partialEvalBinary ApplyG

pattern ApplyGTerm :: (Typeable a, Typeable b) => Term (a --> b) -> Term a -> Term b
pattern ApplyGTerm l r <- BinaryTermPatt ApplyG l r
