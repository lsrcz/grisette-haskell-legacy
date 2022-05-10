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

module Grisette.Data.Prim.Num
  ( pattern NumConcTerm,
    pattern NumOrdConcTerm,
    AddNum (..),
    addNum,
    pattern AddNumTerm,
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
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax.Compat
import Data.Hashable
import Unsafe.Coerce
import Grisette.Data.Prim.Utils

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
data AddNum x where
  AddNum :: (Num x) => AddNum x

instance Eq (AddNum x) where
  _ == _ = True

instance Hashable (AddNum x) where
  s `hashWithSalt` _ = s `hashWithSalt` typeRep (Proxy @AddNum)

instance Show (AddNum x) where
  show AddNum = "AddNum"

instance Lift (AddNum x) where
  liftTyped AddNum = [||AddNum||]
  lift = unTypeSplice . liftTyped

instance NFData (AddNum x) where
  rnf AddNum = ()

addNum :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Term a
addNum l r = normalizeAddNum $ partialEvalBinary @(AddNum a) AddNum l r

instance (Num a, SupportedPrim a) => BinaryCommPartialStrategy (AddNum a) a a where
  singleConstantHandler _ 0 k = Just k
  singleConstantHandler _ l (AddNumTerm (NumConcTerm j) k) = Just $ addNum (concTerm $ l + j) k
  -- singleConstantHandler _ l (TimesNumTerm (NumConcTerm j) k) = Just $ addNum (concTerm $ l * j) (timesNum (concTerm l) k)
  singleConstantHandler _ _ (TimesNumTerm (_ :: Term a) (ConcTerm _ _)) = error "Should not happen"
  singleConstantHandler _ _ (AddNumTerm (_ :: Term a) (ConcTerm _ _)) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryPartialStrategy (AddNum a) a a a where
  extractora _ = numConcTermView
  extractorb _ = numConcTermView
  allConstantHandler _ i j = Just $ concTerm $ i + j

  nonBinaryConstantHandler _ (AddNumTerm i@ConcTerm {} j) k = Just $ addNum i $ addNum j k
  nonBinaryConstantHandler _ i (AddNumTerm j@ConcTerm {} k) = Just $ addNum j $ addNum i k
  nonBinaryConstantHandler _ (UMinusNumTerm i) (UMinusNumTerm j) = Just $ uminusNum $ addNum i j
  nonBinaryConstantHandler _ (TimesNumTerm (ConcTerm _ i) j) (TimesNumTerm (ConcTerm _ k) l)
    | j == l = Just $ timesNum (concTerm $ i + k) j
  nonBinaryConstantHandler _ (TimesNumTerm i@ConcTerm {} j) (TimesNumTerm k@(ConcTerm _ _) l)
    | i == k = Just $ timesNum i (addNum j l)
  nonBinaryConstantHandler _ i j@ConcTerm {} = Just $ addNum j i
  nonBinaryConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryOp (AddNum a) a a a where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(+ " ++ pformat l ++ " " ++ pformat r ++ ")"

normalizeAddNum :: forall a. (Num a, Typeable a) => Term a -> Term a
normalizeAddNum (AddNumTerm (l :: Term a) r@(ConcTerm _ _)) = addNum r l
normalizeAddNum v = v

pattern AddNumTerm :: forall b a. (Typeable b) => Num b => Term b -> Term b -> Term a
pattern AddNumTerm l r <- BinaryTermPatt (AddNum :: AddNum b) l r

minusNum :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
minusNum l r = addNum l (uminusNum r)

-- uminus
data UMinusNum = UMinusNum deriving (Show, Lift, Generic, NFData, Eq, Hashable)

uminusNum :: (Num a, SupportedPrim a) => Term a -> Term a
uminusNum = partialEvalUnary UMinusNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy UMinusNum a a where
  extractor _ = numConcTermView
  constantHandler _ i = Just $ concTerm $ - i
  nonConstantHandler _ (UMinusNumTerm v) = Just v
  -- nonConstantHandler (MinusITerm l r) = Just $ minusi r l
  nonConstantHandler _ (AddNumTerm (NumConcTerm l) r) = Just $ minusNum (concTerm $ - l) r
  nonConstantHandler _ (AddNumTerm (UMinusNumTerm l) r) = Just $ addNum l (uminusNum r)
  nonConstantHandler _ (AddNumTerm l (UMinusNumTerm r)) = Just $ addNum (uminusNum l) r
  nonConstantHandler _ (TimesNumTerm (NumConcTerm l) r) = Just $ timesNum (concTerm $ - l) r
  nonConstantHandler _ (TimesNumTerm (UMinusNumTerm (_ :: Term a)) (_ :: Term a)) = error "Should not happen"
  nonConstantHandler _ (TimesNumTerm (_ :: Term a) (UMinusNumTerm (_ :: Term a))) = error "Should not happen"
  nonConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
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
  singleConstantHandler _ l (AddNumTerm (NumConcTerm j) k) = Just $ addNum (concTerm $ l * j) (timesNum (concTerm l) k)
  singleConstantHandler _ l (UMinusNumTerm j) = Just (timesNum (concTerm $ - l) j)
  singleConstantHandler _ _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen"
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
  leftConstantHandler _ l (AddNumTerm (ConcTerm _ (j :: Integer)) k) = Just $ ltNum (concTerm $ unsafeCoerce l - j) k
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ (AddNumTerm (ConcTerm _ (i :: Integer)) j) k = Just $ ltNum j (concTerm $ unsafeCoerce k - i)
  rightConstantHandler _ l r =
    case eqT @a @Integer of
      Just Refl ->
        Just $ ltNum (concTerm $ - r) (uminusNum l)
      _ -> Nothing

  nonBinaryConstantHandler _ (AddNumTerm (ConcTerm _ (j :: Integer)) k) l = Just $ ltNum (concTerm j) (minusNum (unsafeCoerce l) k)
  nonBinaryConstantHandler _ j (AddNumTerm (ConcTerm _ (k :: Integer)) l) = Just $ ltNum (concTerm $ - k) (minusNum l (unsafeCoerce j))
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
  leftConstantHandler _ l (AddNumTerm (ConcTerm _ (j :: Integer)) k) = Just $ leNum (concTerm $ unsafeCoerce l - j) k
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ (AddNumTerm (ConcTerm _ (i :: Integer)) j) k = Just $ leNum j (concTerm $ unsafeCoerce k - i)
  rightConstantHandler _ l r =
    case eqT @a @Integer of
      Just Refl ->
        Just $ leNum (concTerm $ - r) (uminusNum l)
      _ -> Nothing

  nonBinaryConstantHandler _ (AddNumTerm (ConcTerm _ (j :: Integer)) k) l = Just $ leNum (concTerm j) (minusNum (unsafeCoerce l) k)
  nonBinaryConstantHandler _ j (AddNumTerm (ConcTerm _ (k :: Integer)) l) = Just $ leNum (concTerm $ - k) (minusNum l (unsafeCoerce j))
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
