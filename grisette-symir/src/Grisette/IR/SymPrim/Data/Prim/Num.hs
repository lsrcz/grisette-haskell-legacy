{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.IR.SymPrim.Data.Prim.Num
  ( pattern NumConcTerm,
    pattern NumOrdConcTerm,
    pevalAddNumTerm,
    pevalMinusNumTerm,
    pevalTimesNumTerm,
    pevalUMinusNumTerm,
    pevalAbsNumTerm,
    pevalSignumNumTerm,
    pattern TimesNumTerm,
    LTNum (..),
    ltNum,
    pattern LTNumTerm,
    LENum (..),
    leNum,
    pattern LENumTerm,
    gtNum,
    geNum,
  )
where

import Control.DeepSeq
import Data.Hashable
import Data.Typeable
import GHC.Generics
import Grisette.IR.SymPrim.Data.Prim.Helpers
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.Prim.PartialEval
import Grisette.IR.SymPrim.Data.Prim.Unfold
import Grisette.IR.SymPrim.Data.Prim.Utils
import Language.Haskell.TH.Syntax
import Unsafe.Coerce

numConcTermView :: (Num b, Typeable b) => Term a -> Maybe b
numConcTermView (ConcTerm _ b) = cast b
numConcTermView _ = Nothing

pattern NumConcTerm :: forall b a. (Num b, Typeable b) => b -> Term a
pattern NumConcTerm b <- (numConcTermView -> Just b)

numOrdConcTermView :: (Num b, Ord b, Typeable b) => Term a -> Maybe b
numOrdConcTermView (ConcTerm _ b) = cast b
numOrdConcTermView _ = Nothing

pattern NumOrdConcTerm :: forall b a. (Num b, Ord b, Typeable b) => b -> Term a
pattern NumOrdConcTerm b <- (numOrdConcTermView -> Just b)

-- add
pevalAddNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Term a
pevalAddNumTerm = binaryUnfoldOnce doPevalAddNumTerm (\a b -> normalizeAddNum $ addNumTerm a b)

doPevalAddNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Maybe (Term a)
doPevalAddNumTerm (ConcTerm _ a) (ConcTerm _ b) = Just $ concTerm $ a + b
doPevalAddNumTerm l@(ConcTerm _ a) b = case (a, b) of
  (0, k) -> Just k
  (l1, AddNumTerm _ (ConcTerm _ j) k) -> Just $ pevalAddNumTerm (concTerm $ l1 + j) k
  _ -> doPevalAddNumTermNoConc l b
doPevalAddNumTerm a r@(ConcTerm _ _) = doPevalAddNumTerm r a
doPevalAddNumTerm l r = doPevalAddNumTermNoConc l r

doPevalAddNumTermNoConc :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Maybe (Term a)
doPevalAddNumTermNoConc (AddNumTerm _ i@ConcTerm {} j) k = Just $ pevalAddNumTerm i $ pevalAddNumTerm j k
doPevalAddNumTermNoConc i (AddNumTerm _ j@ConcTerm {} k) = Just $ pevalAddNumTerm j $ pevalAddNumTerm i k
doPevalAddNumTermNoConc (UMinusNumTerm _ i) (UMinusNumTerm _ j) = Just $ pevalUMinusNumTerm $ pevalAddNumTerm i j
doPevalAddNumTermNoConc (TimesNumTerm _ (ConcTerm _ i) j) (TimesNumTerm _ (ConcTerm _ k) l)
  | j == l = Just $ pevalTimesNumTerm (concTerm $ i + k) j
doPevalAddNumTermNoConc (TimesNumTerm _ i@ConcTerm {} j) (TimesNumTerm _ k@(ConcTerm _ _) l)
  | i == k = Just $ pevalTimesNumTerm i (pevalAddNumTerm j l)
doPevalAddNumTermNoConc _ _ = Nothing

normalizeAddNum :: forall a. (Num a, Typeable a) => Term a -> Term a
normalizeAddNum (AddNumTerm _ l r@(ConcTerm _ _)) = addNumTerm r l
normalizeAddNum v = v

pevalMinusNumTerm :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
pevalMinusNumTerm l r = pevalAddNumTerm l (pevalUMinusNumTerm r)

-- uminus
pevalUMinusNumTerm :: (Num a, SupportedPrim a) => Term a -> Term a
pevalUMinusNumTerm = unaryUnfoldOnce doPevalUMinusNumTerm uminusNumTerm

doPevalUMinusNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Maybe (Term a)
doPevalUMinusNumTerm (ConcTerm _ a) = Just $ concTerm $ - a
doPevalUMinusNumTerm (UMinusNumTerm _ v) = Just v
doPevalUMinusNumTerm (AddNumTerm _ (NumConcTerm l) r) = Just $ pevalMinusNumTerm (concTerm $ - l) r
doPevalUMinusNumTerm (AddNumTerm _ (UMinusNumTerm _ l) r) = Just $ pevalAddNumTerm l (pevalUMinusNumTerm r)
doPevalUMinusNumTerm (AddNumTerm _ l (UMinusNumTerm _ r)) = Just $ pevalAddNumTerm (pevalUMinusNumTerm l) r
doPevalUMinusNumTerm (TimesNumTerm _ (NumConcTerm l) r) = Just $ pevalTimesNumTerm (concTerm $ - l) r
doPevalUMinusNumTerm (TimesNumTerm _ (UMinusNumTerm _ _ :: Term a) (_ :: Term a)) = error "Should not happen"
doPevalUMinusNumTerm (TimesNumTerm _ (_ :: Term a) (UMinusNumTerm _ (_ :: Term a))) = error "Should not happen"
doPevalUMinusNumTerm (AddNumTerm _ (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
doPevalUMinusNumTerm _ = Nothing

-- times
pevalTimesNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Term a
pevalTimesNumTerm = binaryUnfoldOnce doPevalTimesNumTerm (\a b -> normalizeTimesNum $ timesNumTerm a b)

normalizeTimesNum :: forall a. (Num a, Typeable a) => Term a -> Term a
normalizeTimesNum (TimesNumTerm _ l r@(ConcTerm _ _)) = timesNumTerm r l
normalizeTimesNum v = v

doPevalTimesNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Maybe (Term a)
doPevalTimesNumTerm (ConcTerm _ a) (ConcTerm _ b) = Just $ concTerm $ a * b
doPevalTimesNumTerm l@(ConcTerm _ a) b = case (a, b) of
  (0, _) -> Just $ concTerm 0
  (1, k) -> Just k
  (-1, k) -> Just $ pevalUMinusNumTerm k
  (l1, TimesNumTerm _ (NumConcTerm j) k) -> Just $ pevalTimesNumTerm (concTerm $ l1 * j) k
  (l1, AddNumTerm _ (NumConcTerm j) k) -> Just $ pevalAddNumTerm (concTerm $ l1 * j) (pevalTimesNumTerm (concTerm l1) k)
  (l1, UMinusNumTerm _ j) -> Just (pevalTimesNumTerm (concTerm $ - l1) j)
  (_, TimesNumTerm _ (_ :: Term a) ConcTerm {}) -> error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  (_, AddNumTerm _ (_ :: Term a) ConcTerm {}) -> error "Should not happen"
  _ -> doPevalTimesNumTermNoConc l b
doPevalTimesNumTerm a r@(ConcTerm _ _) = doPevalTimesNumTerm r a
doPevalTimesNumTerm l r = doPevalTimesNumTermNoConc l r

doPevalTimesNumTermNoConc :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Maybe (Term a)
doPevalTimesNumTermNoConc (TimesNumTerm _ i@ConcTerm {} j) k = Just $ pevalTimesNumTerm i $ pevalTimesNumTerm j k
doPevalTimesNumTermNoConc i (TimesNumTerm _ j@ConcTerm {} k) = Just $ pevalTimesNumTerm j $ pevalTimesNumTerm i k
doPevalTimesNumTermNoConc (UMinusNumTerm _ i) j = Just $ pevalUMinusNumTerm $ pevalTimesNumTerm i j
doPevalTimesNumTermNoConc i (UMinusNumTerm _ j) = Just $ pevalUMinusNumTerm $ pevalTimesNumTerm i j
doPevalTimesNumTermNoConc i j@ConcTerm {} = Just $ pevalTimesNumTerm j i
doPevalTimesNumTermNoConc (TimesNumTerm _ (_ :: Term a) ConcTerm {}) _ = error "Should not happen" -- Just $ addi j $ addi i k
doPevalTimesNumTermNoConc _ (TimesNumTerm _ (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi k $ addi i j
doPevalTimesNumTermNoConc _ _ = Nothing

{-
pevalTimesNumTerm :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
pevalTimesNumTerm = partialEvalBinary TimesNum

instance (Num a, SupportedPrim a) => BinaryCommPartialStrategy TimesNum a a where
  singleConstantHandler _ 0 _ = Just $ concTerm 0
  singleConstantHandler _ 1 k = Just k
  singleConstantHandler _ (-1) k = Just $ pevalUMinusNumTerm k
  singleConstantHandler _ l (TimesNumTerm (NumConcTerm j) k) = Just $ pevalTimesNumTerm (concTerm $ l * j) k
  singleConstantHandler _ l (AddNumTerm _ (NumConcTerm j) k) = Just $ pevalAddNumTerm (concTerm $ l * j) (pevalTimesNumTerm (concTerm l) k)
  singleConstantHandler _ l (UMinusNumTerm _ j) = Just (pevalTimesNumTerm (concTerm $ - l) j)
  singleConstantHandler _ _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ _ (AddNumTerm _ (_ :: Term a) ConcTerm {}) = error "Should not happen"
  singleConstantHandler _ _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryPartialStrategy TimesNum a a a where
  extractora _ = numConcTermView
  extractorb _ = numConcTermView
  allConstantHandler _ i j = Just $ concTerm $ i * j

  nonBinaryConstantHandler _ (TimesNumTerm i@ConcTerm {} j) k = Just $ pevalTimesNumTerm i $ pevalTimesNumTerm j k
  nonBinaryConstantHandler _ i (TimesNumTerm j@ConcTerm {} k) = Just $ pevalTimesNumTerm j $ pevalTimesNumTerm i k
  nonBinaryConstantHandler _ (UMinusNumTerm _ i) j = Just $ pevalUMinusNumTerm $ pevalTimesNumTerm i j
  nonBinaryConstantHandler _ i (UMinusNumTerm _ j) = Just $ pevalUMinusNumTerm $ pevalTimesNumTerm i j
  nonBinaryConstantHandler _ i j@ConcTerm {} = Just $ pevalTimesNumTerm j i
  nonBinaryConstantHandler _ (TimesNumTerm (_ :: Term a) ConcTerm {}) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryOp TimesNum a a a where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(* " ++ pformat l ++ " " ++ pformat r ++ ")"
  -}

-- abs
pevalAbsNumTerm :: (SupportedPrim a, Num a) => Term a -> Term a
pevalAbsNumTerm = unaryUnfoldOnce doPevalAbsNumTerm absNumTerm

doPevalAbsNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Maybe (Term a)
doPevalAbsNumTerm (ConcTerm _ a) = Just $ concTerm $ abs a
doPevalAbsNumTerm (UMinusNumTerm _ v) = Just $ pevalAbsNumTerm v
doPevalAbsNumTerm t@(AbsNumTerm _ (_ :: Term a)) = Just t
doPevalAbsNumTerm (TimesNumTerm _ (Dyn (l :: Term Integer)) r) =
  Just $ pevalTimesNumTerm (pevalAbsNumTerm $ unsafeCoerce l :: Term a) $ pevalAbsNumTerm (unsafeCoerce r)
-- nonConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
doPevalAbsNumTerm _ = Nothing

-- signum

pevalSignumNumTerm :: (Num a, SupportedPrim a) => Term a -> Term a
pevalSignumNumTerm = unaryUnfoldOnce doPevalSignumNumTerm signumNumTerm

doPevalSignumNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Maybe (Term a)
doPevalSignumNumTerm (ConcTerm _ a) = Just $ concTerm $ signum a
-- doPevalSignumNumTerm (UMinusNumTerm v) = Just $ pevalUMinusNumTerm $ signumNum v
doPevalSignumNumTerm (UMinusNumTerm _ (Dyn (v :: Term Integer))) = Just $ pevalUMinusNumTerm $ pevalSignumNumTerm $ unsafeCoerce v
-- doPevalSignumNumTerm (TimesNumTerm l r) = Just $ pevalTimesNumTerm (signumNum l) $ signumNum r
doPevalSignumNumTerm (TimesNumTerm _ (Dyn (l :: Term Integer)) r) =
  Just $ pevalTimesNumTerm (pevalSignumNumTerm $ unsafeCoerce l :: Term a) $ pevalSignumNumTerm (unsafeCoerce r)
-- doPevalSignumNumTerm (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
doPevalSignumNumTerm _ = Nothing

-- lt
data LTNum = LTNum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

ltNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
ltNum = partialEvalBinary LTNum

instance (Num a, Ord a, SupportedPrim a) => BinaryPartialStrategy LTNum a a Bool where
  extractora _ = numOrdConcTermView
  extractorb _ = numOrdConcTermView
  allConstantHandler _ l r = Just $ concTerm $ l < r
  leftConstantHandler _ l (AddNumTerm _ (ConcTerm _ (Dyn (j :: Integer))) k) = Just $ ltNum (concTerm $ unsafeCoerce l - j) (unsafeCoerce k)
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ (AddNumTerm _ (ConcTerm _ (Dyn (i :: Integer))) j) k = Just $ ltNum (unsafeCoerce j) (concTerm $ unsafeCoerce k - i)
  rightConstantHandler _ l r =
    case eqT @a @Integer of
      Just Refl ->
        Just $ ltNum (concTerm $ - r) (pevalUMinusNumTerm l)
      _ -> Nothing

  nonBinaryConstantHandler _ (AddNumTerm _ (ConcTerm _ (Dyn (j :: Integer))) k) l = Just $ ltNum (concTerm j) (pevalMinusNumTerm (unsafeCoerce l) (unsafeCoerce k))
  nonBinaryConstantHandler _ j (AddNumTerm _ (ConcTerm _ (Dyn (k :: Integer))) l) = Just $ ltNum (concTerm $ - k) (pevalMinusNumTerm (unsafeCoerce l) (unsafeCoerce j))
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Num a, Ord a, SupportedPrim a) => BinaryOp LTNum a a Bool where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(< " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern LTNumTerm :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
pattern LTNumTerm l r <- BinaryTermPatt LTNum l r

-- le
data LENum = LENum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

leNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
leNum = partialEvalBinary LENum

instance (Num a, Ord a, SupportedPrim a) => BinaryPartialStrategy LENum a a Bool where
  extractora _ = numOrdConcTermView
  extractorb _ = numOrdConcTermView
  allConstantHandler _ l r = Just $ concTerm $ l <= r
  leftConstantHandler _ l (AddNumTerm _ (ConcTerm _ (Dyn (j :: Integer))) k) = Just $ leNum (concTerm $ unsafeCoerce l - j) (unsafeCoerce k)
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ (AddNumTerm _ (ConcTerm _ (Dyn (i :: Integer))) j) k = Just $ leNum (unsafeCoerce j) (concTerm $ unsafeCoerce k - i)
  rightConstantHandler _ l r =
    case eqT @a @Integer of
      Just Refl ->
        Just $ leNum (concTerm $ - r) (pevalUMinusNumTerm l)
      _ -> Nothing

  nonBinaryConstantHandler _ (AddNumTerm _ (ConcTerm _ (Dyn (j :: Integer))) k) l = Just $ leNum (concTerm j) (pevalMinusNumTerm (unsafeCoerce l) (unsafeCoerce k))
  nonBinaryConstantHandler _ j (AddNumTerm _ (ConcTerm _ (Dyn (k :: Integer))) l) = Just $ leNum (concTerm $ - k) (pevalMinusNumTerm (unsafeCoerce l) (unsafeCoerce j))
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Num a, Ord a, SupportedPrim a) => BinaryOp LENum a a Bool where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(<= " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern LENumTerm :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
pattern LENumTerm l r <- BinaryTermPatt LENum l r

gtNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
gtNum = flip ltNum

geNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
geNum = flip leNum
