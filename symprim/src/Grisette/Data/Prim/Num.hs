{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
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

instance Show (AddNum x) where
  show AddNum = "AddNum"

instance Lift (AddNum x) where
  lift AddNum = [|AddNum|]
  liftTyped = unsafeTExpCoerce . lift

instance NFData (AddNum x) where
  rnf AddNum = ()

addNum :: forall a. (Num a, SupportedPrim a) => Term a -> Term a -> Term a
addNum l r = normalizeAddNum $ partialEvalBinary @(AddNum a) AddNum l r

instance (Num a, SupportedPrim a) => BinaryCommPartialStrategy (AddNum a) a a where
  singleConstantHandler 0 k = Just k
  singleConstantHandler l (AddNumTerm (NumConcTerm j) k) = Just $ addNum (concTerm $ l + j) k
  singleConstantHandler l (TimesNumTerm (NumConcTerm j) k) = Just $ addNum (concTerm $ l * j) (timesNum (concTerm l) k)
  singleConstantHandler _ (TimesNumTerm (_ :: Term a) (ConcTerm _ _)) = error "Should not happen"
  singleConstantHandler _ (AddNumTerm (_ :: Term a) (ConcTerm _ _)) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryPartialStrategy (AddNum a) a a a where
  extractora = numConcTermView
  extractorb = numConcTermView
  allConstantHandler i j = Just $ concTerm $ i + j

  nonBinaryConstantHandler (AddNumTerm i@ConcTerm {} j) k = Just $ addNum i $ addNum j k
  nonBinaryConstantHandler i (AddNumTerm j@ConcTerm {} k) = Just $ addNum j $ addNum i k
  nonBinaryConstantHandler (UMinusNumTerm i) (UMinusNumTerm j) = Just $ uminusNum $ addNum i j
  nonBinaryConstantHandler (TimesNumTerm i@ConcTerm {} j) (TimesNumTerm k@(ConcTerm _ _) l)
    | i == k = Just $ timesNum i (addNum j l)
  nonBinaryConstantHandler i j@ConcTerm {} = Just $ addNum j i
  nonBinaryConstantHandler (AddNumTerm (_ :: Term a) ConcTerm {}) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryOp (AddNum a) a a a where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @(AddNum a)) (constructBinary @(AddNum a) AddNum) l r
  pformatBinary l r = "(+ " ++ pformat l ++ " " ++ pformat r ++ ")"

normalizeAddNum :: forall a. (Num a, Typeable a) => Term a -> Term a
normalizeAddNum (AddNumTerm (l :: Term a) r@(ConcTerm _ _)) = addNum r l
normalizeAddNum v = v

pattern AddNumTerm :: forall b a. (Typeable b) => Num b => Term b -> Term b -> Term a
pattern AddNumTerm l r <- BinaryTermPatt (AddNum :: AddNum b) l r

minusNum :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
minusNum l r = addNum l (uminusNum r)

-- uminus
data UMinusNum = UMinusNum deriving (Show, Lift, Generic, NFData)

uminusNum :: (Num a, SupportedPrim a) => Term a -> Term a
uminusNum = partialEvalUnary UMinusNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy UMinusNum a a where
  extractor = numConcTermView
  constantHandler i = Just $ concTerm $ - i
  nonConstantHandler (UMinusNumTerm v) = Just v
  -- nonConstantHandler (MinusITerm l r) = Just $ minusi r l
  nonConstantHandler (AddNumTerm (NumConcTerm l) r) = Just $ minusNum (concTerm $ - l) r
  nonConstantHandler (AddNumTerm (UMinusNumTerm l) r) = Just $ addNum l (uminusNum r)
  nonConstantHandler (AddNumTerm l (UMinusNumTerm r)) = Just $ addNum (uminusNum l) r
  nonConstantHandler (TimesNumTerm (NumConcTerm l) r) = Just $ timesNum (concTerm $ - l) r
  nonConstantHandler (TimesNumTerm (UMinusNumTerm (_ :: Term a)) (_ :: Term a)) = error "Should not happen"
  nonConstantHandler (TimesNumTerm (_ :: Term a) (UMinusNumTerm (_ :: Term a))) = error "Should not happen"
  nonConstantHandler (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ = Nothing

instance (Num a, SupportedPrim a) => UnaryOp UMinusNum a a where
  partialEvalUnary _ v = unaryUnfoldOnce (unaryPartial @UMinusNum) (constructUnary UMinusNum) v
  pformatUnary v = "(- " ++ pformat v ++ ")"

pattern UMinusNumTerm :: (Num b, Typeable b) => Term b -> Term a
pattern UMinusNumTerm v <- UnaryTermPatt UMinusNum v

-- times
data TimesNum = TimesNum deriving (Show, Lift, Generic, NFData)

timesNum :: (Num a, SupportedPrim a) => Term a -> Term a -> Term a
timesNum = partialEvalBinary TimesNum

instance (Num a, SupportedPrim a) => BinaryCommPartialStrategy TimesNum a a where
  singleConstantHandler 0 _ = Just $ concTerm 0
  singleConstantHandler 1 k = Just k
  singleConstantHandler (-1) k = Just $ uminusNum k
  singleConstantHandler l (TimesNumTerm (NumConcTerm j) k) = Just $ timesNum (concTerm $ l * j) k
  singleConstantHandler l (AddNumTerm (NumConcTerm j) k) = Just $ addNum (concTerm $ l * j) (timesNum (concTerm l) k)
  singleConstantHandler l (UMinusNumTerm j) = Just (timesNum (concTerm $ - l) j)
  singleConstantHandler _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen"
  singleConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryPartialStrategy TimesNum a a a where
  extractora = numConcTermView
  extractorb = numConcTermView
  allConstantHandler i j = Just $ concTerm $ i * j

  nonBinaryConstantHandler (TimesNumTerm i@ConcTerm {} j) k = Just $ timesNum i $ timesNum j k
  nonBinaryConstantHandler i (TimesNumTerm j@ConcTerm {} k) = Just $ timesNum j $ timesNum i k
  nonBinaryConstantHandler (UMinusNumTerm i) j = Just $ uminusNum $ timesNum i j
  nonBinaryConstantHandler i (UMinusNumTerm j) = Just $ uminusNum $ timesNum i j
  nonBinaryConstantHandler i j@ConcTerm {} = Just $ timesNum j i
  nonBinaryConstantHandler (TimesNumTerm (_ :: Term a) ConcTerm {}) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ (TimesNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ = Nothing

instance (Num a, SupportedPrim a) => BinaryOp TimesNum a a a where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @TimesNum) (constructBinary TimesNum) l r
  pformatBinary l r = "(* " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern TimesNumTerm :: (Num b, Typeable b) => Term b -> Term b -> Term a
pattern TimesNumTerm l r <- BinaryTermPatt TimesNum l r

-- abs
data AbsNum = AbsNum deriving (Show, Lift, Generic, NFData)

absNum :: (SupportedPrim a, Num a) => Term a -> Term a
absNum = partialEvalUnary AbsNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy AbsNum a a where
  extractor = numConcTermView
  constantHandler i = Just $ concTerm $ abs i
  nonConstantHandler (UMinusNumTerm v) = Just $ absNum v
  nonConstantHandler t@(AbsNumTerm (_ :: Term a)) = Just t
  nonConstantHandler (TimesNumTerm l r) = Just $ timesNum (absNum l) $ absNum r
  nonConstantHandler (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ = Nothing

instance (Num a, SupportedPrim a) => UnaryOp AbsNum a a where
  partialEvalUnary _ v = unaryUnfoldOnce (unaryPartial @AbsNum) (constructUnary AbsNum) v
  pformatUnary v = "(absI " ++ pformat v ++ ")"

pattern AbsNumTerm :: (Num b, SupportedPrim b) => Term b -> Term a
pattern AbsNumTerm v <- UnaryTermPatt AbsNum v

-- signum
data SignumNum = SignumNum deriving (Show, Lift, Generic, NFData)

signumNum :: (Num a, SupportedPrim a) => Term a -> Term a
signumNum = partialEvalUnary SignumNum

instance (Num a, SupportedPrim a) => UnaryPartialStrategy SignumNum a a where
  extractor = numConcTermView
  constantHandler i = Just $ concTerm $ signum i
  nonConstantHandler (UMinusNumTerm v) = Just $ uminusNum $ signumNum v
  nonConstantHandler (TimesNumTerm l r) = Just $ timesNum (signumNum l) $ signumNum r
  nonConstantHandler (AddNumTerm (_ :: Term a) ConcTerm {}) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ = Nothing

instance (Num a, SupportedPrim a) => UnaryOp SignumNum a a where
  partialEvalUnary _ v = unaryUnfoldOnce (unaryPartial @SignumNum) (constructUnary SignumNum) v
  pformatUnary v = "(signumI " ++ pformat v ++ ")"

pattern SignumNumTerm :: (Num b, SupportedPrim b) => Term b -> Term a
pattern SignumNumTerm v <- UnaryTermPatt SignumNum v

-- lt
data LTNum = LTNum deriving (Show, Lift, Generic, NFData)

ltNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
ltNum = partialEvalBinary LTNum

instance (Num a, Ord a, SupportedPrim a) => BinaryPartialStrategy LTNum a a Bool where
  extractora = numOrdConcTermView
  extractorb = numOrdConcTermView
  allConstantHandler l r = Just $ concTerm $ l < r
  leftConstantHandler l (AddNumTerm (NumOrdConcTerm j) k) = Just $ ltNum (concTerm $ l - j) k
  -- leftConstantHandler l (UMinusITerm j) = Just $ lti j $ concTerm $ -l
  leftConstantHandler _ (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) = error "Should not happen" -- Just $ lti (concTerm $ l - k) j
  leftConstantHandler _ _ = Nothing
  rightConstantHandler (AddNumTerm (NumOrdConcTerm i) j) k = Just $ ltNum j (concTerm $ k - i)
  rightConstantHandler (UMinusNumTerm i) j = Just $ ltNum (concTerm $ - j) i
  rightConstantHandler (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) _ = error "Should not happen" -- Just $ lti i (concTerm $ k - j)
  rightConstantHandler l r = Just $ ltNum (concTerm $ - r) (uminusNum l)

  nonBinaryConstantHandler (AddNumTerm (NumOrdConcTerm j) k) l = Just $ ltNum (concTerm j) (minusNum k l)
  nonBinaryConstantHandler j (AddNumTerm (NumOrdConcTerm k) l) = Just $ ltNum (concTerm $ - k) (minusNum l j)
  nonBinaryConstantHandler (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) _ = error "Should not happen" -- Just $ lti (concTerm k) (minusi j l)
  nonBinaryConstantHandler _ (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) = error "Should not happen" -- Just $ lti (concTerm $ -l) (minusi k j)
  nonBinaryConstantHandler _ _ = Nothing

instance (Num a, Ord a, SupportedPrim a) => BinaryOp LTNum a a Bool where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @LTNum) (constructBinary LTNum) l r
  pformatBinary l r = "(< " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern LTNumTerm :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
pattern LTNumTerm l r <- BinaryTermPatt LTNum l r

-- le
data LENum = LENum deriving (Show, Lift, Generic, NFData)

leNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
leNum = partialEvalBinary LENum

instance (Num a, Ord a, SupportedPrim a) => BinaryPartialStrategy LENum a a Bool where
  extractora = numOrdConcTermView
  extractorb = numOrdConcTermView
  allConstantHandler l r = Just $ concTerm $ l <= r
  leftConstantHandler l (AddNumTerm (NumOrdConcTerm j) k) = Just $ leNum (concTerm $ l - j) k
  leftConstantHandler _ (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) = error "Should not happen" -- Just $ lti (concTerm $ l - k) j
  leftConstantHandler _ _ = Nothing
  rightConstantHandler (AddNumTerm (NumOrdConcTerm i) j) k = Just $ leNum j (concTerm $ k - i)
  rightConstantHandler (UMinusNumTerm i) j = Just $ leNum (concTerm $ - j) i
  rightConstantHandler (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) _ = error "Should not happen" -- Just $ lti i (concTerm $ k - j)
  rightConstantHandler l r = Just $ leNum (concTerm $ - r) (uminusNum l)

  nonBinaryConstantHandler (AddNumTerm (NumOrdConcTerm j) k) l = Just $ leNum (concTerm j) (minusNum k l)
  nonBinaryConstantHandler j (AddNumTerm (NumOrdConcTerm k) l) = Just $ leNum (concTerm $ - k) (minusNum l j)
  nonBinaryConstantHandler (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) _ = error "Should not happen" -- Just $ lti (concTerm k) (minusi j l)
  nonBinaryConstantHandler _ (AddNumTerm (_ :: Term a) (NumOrdConcTerm (_ :: a))) = error "Should not happen" -- Just $ lti (concTerm $ -l) (minusi k j)
  nonBinaryConstantHandler _ _ = Nothing

instance (Num a, Ord a, SupportedPrim a) => BinaryOp LENum a a Bool where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @LENum) (constructBinary LENum) l r
  pformatBinary l r = "(<= " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern LENumTerm :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
pattern LENumTerm l r <- BinaryTermPatt LENum l r

gtNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
gtNum = flip ltNum

geNum :: (Num a, Ord a, SupportedPrim a) => Term a -> Term a -> Term Bool
geNum = flip leNum
