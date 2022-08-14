{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.IR.SymPrim.Data.Prim.Num
  ( pattern NumConcTerm,
    pattern NumOrdConcTerm,
    pevalAddNumTerm,
    minusNum,
    UMinusNum (..),
    uminusNum,
    pattern UMinusNumTerm,
    AbsNum (..),
    absNum,
    pattern AbsNumTerm,
    SignumNum (..),
    signumNum,
    pattern SignumNumTerm,
    TimesNum (..),
    timesNum,
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
import Data.Typeable
import GHC.Generics
import Grisette.IR.SymPrim.Data.Prim.Helpers
import Grisette.IR.SymPrim.Data.Prim.PartialEval
import Grisette.IR.SymPrim.Data.Prim.Unfold
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Language.Haskell.TH.Syntax
import Data.Hashable
import Unsafe.Coerce
import Grisette.IR.SymPrim.Data.Prim.Utils

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
pevalAddNumTerm l r = binaryUnfoldOnce doPevalAddNumTerm (\a b -> normalizeAddNum $ addNumTerm a b) l r

doPevalAddNumTerm :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Maybe (Term a)
doPevalAddNumTerm (ConcTerm _ a) (ConcTerm _ b) = Just $ concTerm $ a + b
doPevalAddNumTerm l@(ConcTerm _ a) b = case (a, b) of
  (0, k) -> Just k
  (l, (AddNumTerm _ (ConcTerm _ j) k)) -> Just $ pevalAddNumTerm (concTerm $ l + j) k
  _ -> doPevalAddNumTermNoConc l b
doPevalAddNumTerm a r@(ConcTerm _ _) = doPevalAddNumTerm r a
doPevalAddNumTerm l r = doPevalAddNumTermNoConc l r

doPevalAddNumTermNoConc :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Maybe (Term a)
doPevalAddNumTermNoConc (AddNumTerm _ i@ConcTerm {} j) k = Just $ pevalAddNumTerm i $ pevalAddNumTerm j k
doPevalAddNumTermNoConc i (AddNumTerm _ j@ConcTerm {} k) = Just $ pevalAddNumTerm j $ pevalAddNumTerm i k
doPevalAddNumTermNoConc (UMinusNumTerm i) (UMinusNumTerm j) = Just $ uminusNum $ pevalAddNumTerm i j
doPevalAddNumTermNoConc (TimesNumTerm (ConcTerm _ i) j) (TimesNumTerm (ConcTerm _ k) l)
    | j == l = Just $ timesNum (concTerm $ i + k) j
doPevalAddNumTermNoConc (TimesNumTerm i@ConcTerm {} j) (TimesNumTerm k@(ConcTerm _ _) l)
    | i == k = Just $ timesNum i (pevalAddNumTerm j l)
doPevalAddNumTermNoConc i j = Nothing

normalizeAddNum :: forall a. (Num a, Typeable a) => Term a -> Term a
normalizeAddNum (AddNumTerm _ l r@(ConcTerm _ _)) = addNumTerm r l
normalizeAddNum v = v

minusNum :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
minusNum l r = pevalAddNumTerm l (uminusNum r)

-- uminus
data UMinusNum = UMinusNum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

uminusNum :: (Num a, SupportedPrim a) => Term a -> Term a
uminusNum = partialEvalUnary UMinusNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy UMinusNum a a where
  extractor _ = numConcTermView
  constantHandler _ i = Just $ concTerm $ - i
  nonConstantHandler _ (UMinusNumTerm v) = Just v
  -- nonConstantHandler (MinusITerm l r) = Just $ minusi r l
  nonConstantHandler _ (AddNumTerm _ (NumConcTerm l) r) = Just $ minusNum (concTerm $ - l) r
  nonConstantHandler _ (AddNumTerm _ (UMinusNumTerm l) r) = Just $ pevalAddNumTerm l (uminusNum r)
  nonConstantHandler _ (AddNumTerm _ l (UMinusNumTerm r)) = Just $ pevalAddNumTerm (uminusNum l) r
  nonConstantHandler _ (TimesNumTerm (NumConcTerm l) r) = Just $ timesNum (concTerm $ - l) r
  nonConstantHandler _ (TimesNumTerm (UMinusNumTerm (_ :: Term a)) (_ :: Term a)) = error "Should not happen"
  nonConstantHandler _ (TimesNumTerm (_ :: Term a) (UMinusNumTerm (_ :: Term a))) = error "Should not happen"
  nonConstantHandler _ (AddNumTerm _ (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => UnaryOp UMinusNum a a where
  partialEvalUnary tag v = unaryUnfoldOnce (unaryPartial tag) (constructUnary tag) v
  pformatUnary _ v = "(- " ++ pformat v ++ ")"

pattern UMinusNumTerm :: (Num b, Typeable b) => Term b -> Term a
pattern UMinusNumTerm v <- UnaryTermPatt UMinusNum v

-- times
data TimesNum = TimesNum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

timesNum :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
timesNum = partialEvalBinary TimesNum

instance (Num a, SupportedPrim a) => BinaryCommPartialStrategy TimesNum a a where
  singleConstantHandler _ 0 _ = Just $ concTerm 0
  singleConstantHandler _ 1 k = Just k
  singleConstantHandler _ (-1) k = Just $ uminusNum k
  singleConstantHandler _ l (TimesNumTerm (NumConcTerm j) k) = Just $ timesNum (concTerm $ l * j) k
  singleConstantHandler _ l (AddNumTerm _ (NumConcTerm j) k) = Just $ pevalAddNumTerm (concTerm $ l * j) (timesNum (concTerm l) k)
  singleConstantHandler _ l (UMinusNumTerm j) = Just (timesNum (concTerm $ - l) j)
  singleConstantHandler _ _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ _ (AddNumTerm _ (_ :: Term a) ConcTerm {}) = error "Should not happen"
  singleConstantHandler _ _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryPartialStrategy TimesNum a a a where
  extractora _ = numConcTermView
  extractorb _ = numConcTermView
  allConstantHandler _ i j = Just $ concTerm $ i * j

  nonBinaryConstantHandler _ (TimesNumTerm i@ConcTerm {} j) k = Just $ timesNum i $ timesNum j k
  nonBinaryConstantHandler _ i (TimesNumTerm j@ConcTerm {} k) = Just $ timesNum j $ timesNum i k
  nonBinaryConstantHandler _ (UMinusNumTerm i) j = Just $ uminusNum $ timesNum i j
  nonBinaryConstantHandler _ i (UMinusNumTerm j) = Just $ uminusNum $ timesNum i j
  nonBinaryConstantHandler _ i j@ConcTerm {} = Just $ timesNum j i
  nonBinaryConstantHandler _ (TimesNumTerm (_ :: Term a) ConcTerm {}) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryOp TimesNum a a a where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(* " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern TimesNumTerm :: (Num b, Typeable b) => Term b -> Term b -> Term a
pattern TimesNumTerm l r <- BinaryTermPatt TimesNum l r

-- abs
data AbsNum = AbsNum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

absNum :: (SupportedPrim a, Num a) => Term a -> Term a
absNum = partialEvalUnary AbsNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy AbsNum a a where
  extractor _ = numConcTermView
  constantHandler _ i = Just $ concTerm $ abs i
  nonConstantHandler _ (UMinusNumTerm v) = Just $ absNum v
  nonConstantHandler _ t@(AbsNumTerm (_ :: Term a)) = Just t
  nonConstantHandler _ (BinaryTerm _ (Dyn TimesNum) (Dyn (l :: Term Integer)) r) =
    Just $ timesNum (absNum $ unsafeCoerce l :: Term a) $ absNum (unsafeCoerce r)
  -- nonConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => UnaryOp AbsNum a a where
  partialEvalUnary tag v = unaryUnfoldOnce (unaryPartial tag) (constructUnary tag) v
  pformatUnary _ v = "(absI " ++ pformat v ++ ")"

pattern AbsNumTerm :: (Num b, SupportedPrim b) => Term b -> Term a
pattern AbsNumTerm v <- UnaryTermPatt AbsNum v

-- signum
data SignumNum = SignumNum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

signumNum :: (Num a, SupportedPrim a) => Term a -> Term a
signumNum = partialEvalUnary SignumNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy SignumNum a a where
  extractor _ = numConcTermView
  constantHandler _ i = Just $ concTerm $ signum i
  -- nonConstantHandler _ (UMinusNumTerm v) = Just $ uminusNum $ signumNum v
  nonConstantHandler _ (UnaryTerm _ (Dyn UMinusNum) (Dyn (v :: Term Integer))) = Just $ uminusNum $ signumNum $ unsafeCoerce v
  -- nonConstantHandler _ (TimesNumTerm l r) = Just $ timesNum (signumNum l) $ signumNum r
  nonConstantHandler _ (BinaryTerm _ (Dyn TimesNum) (Dyn (l :: Term Integer)) r) =
    Just $ timesNum (signumNum $ unsafeCoerce l :: Term a) $ signumNum (unsafeCoerce r)
  -- nonConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => UnaryOp SignumNum a a where
  partialEvalUnary tag v = unaryUnfoldOnce (unaryPartial tag) (constructUnary tag) v
  pformatUnary _ v = "(signumI " ++ pformat v ++ ")"

pattern SignumNumTerm :: (Num b, SupportedPrim b) => Term b -> Term a
pattern SignumNumTerm v <- UnaryTermPatt SignumNum v

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
        Just $ ltNum (concTerm $ - r) (uminusNum l)
      _ -> Nothing

  nonBinaryConstantHandler _ (AddNumTerm _ (ConcTerm _ (Dyn (j :: Integer))) k) l = Just $ ltNum (concTerm j) (minusNum (unsafeCoerce l) (unsafeCoerce k))
  nonBinaryConstantHandler _ j (AddNumTerm _ (ConcTerm _ (Dyn (k :: Integer))) l) = Just $ ltNum (concTerm $ - k) (minusNum (unsafeCoerce l) (unsafeCoerce j))
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
        Just $ leNum (concTerm $ - r) (uminusNum l)
      _ -> Nothing

  nonBinaryConstantHandler _ (AddNumTerm _ (ConcTerm _ (Dyn (j :: Integer))) k) l = Just $ leNum (concTerm j) (minusNum (unsafeCoerce l) (unsafeCoerce k))
  nonBinaryConstantHandler _ j (AddNumTerm _ (ConcTerm _ (Dyn (k :: Integer))) l) = Just $ leNum (concTerm $ - k) (minusNum (unsafeCoerce l) (unsafeCoerce j))
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
