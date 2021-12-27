{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.Integer
  ( pattern IntegerConcTerm,
    pattern IntegerTerm,
    AddI (..),
    addi,
    minusi,
    pattern AddITerm,
    UMinusI (..),
    uminusi,
    pattern UMinusITerm,
    LTI (..),
    lti,
    gei,
    pattern LTITerm,
    LEI (..),
    lei,
    gti,
    pattern LEITerm,
    TimesI (..),
    timesi,
    pattern TimesITerm,
    DivI (..),
    divi,
    pattern DivITerm,
    ModI (..),
    modi,
    pattern ModITerm,
  )
where

import Data.Typeable
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm

integerConcTermView :: forall a. Term a -> Maybe Integer
integerConcTermView (ConcTerm _ b) = cast b
integerConcTermView _ = Nothing

pattern IntegerConcTerm :: Integer -> Term a
pattern IntegerConcTerm b <- (integerConcTermView -> Just b)

integerTermView :: Term a -> Maybe (Term Integer)
integerTermView = castTerm

pattern IntegerTerm :: Term Integer -> Term a
pattern IntegerTerm b <- (integerTermView -> Just b)

-- add
data AddI = AddI deriving (Show)

normalizeAdd :: Term Integer -> Term Integer
normalizeAdd (AddITerm i j@(IntegerConcTerm _)) = addi j i
normalizeAdd v = v

addi :: Term Integer -> Term Integer -> Term Integer
addi l r = normalizeAdd $ partialEvalBinary AddI l r

instance BinaryCommPartialStrategy AddI Integer Integer where
  singleConstantHandler 0 k = Just k
  singleConstantHandler l (AddITerm (IntegerConcTerm j) k) = Just $ addi (concTerm $ l + j) k
  singleConstantHandler l (TimesITerm (IntegerConcTerm j) k) = Just $ addi (concTerm $ l * j) (timesi (concTerm l) k)
  singleConstantHandler _ (TimesITerm _ (IntegerConcTerm _)) = error "Should not happen"
  singleConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ _ = Nothing

instance BinaryPartialStrategy AddI Integer Integer Integer where
  extractora = integerConcTermView
  extractorb = integerConcTermView
  allConstantHandler i j = Just $ concTerm $ i + j

  nonBinaryConstantHandler (AddITerm i@(IntegerConcTerm _) j) k = Just $ addi i $ addi j k
  nonBinaryConstantHandler i (AddITerm j@(IntegerConcTerm _) k) = Just $ addi j $ addi i k
  nonBinaryConstantHandler (UMinusITerm i) (UMinusITerm j) = Just $ uminusi $ addi i j
  nonBinaryConstantHandler (TimesITerm i@(IntegerConcTerm _) j) (TimesITerm k@(IntegerConcTerm _) l)
    | i == k = Just $ timesi i (addi j l)
  nonBinaryConstantHandler i j@(IntegerConcTerm _) = Just $ addi j i
  nonBinaryConstantHandler (AddITerm _ (IntegerConcTerm _)) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ = Nothing

instance BinaryOp AddI Integer Integer Integer where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @AddI) (constructBinary AddI) l r
  pformatBinary l r = "(+I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern AddITerm :: Term Integer -> Term Integer -> Term a
pattern AddITerm l r <- BinaryTermPatt AddI l r

minusi :: Term Integer -> Term Integer -> Term Integer
minusi l r = addi l (uminusi r)

-- uminus
data UMinusI = UMinusI deriving (Show)

uminusi :: Term Integer -> Term Integer
uminusi = partialEvalUnary UMinusI

instance UnaryPartialStrategy UMinusI Integer Integer where
  extractor = integerConcTermView
  constantHandler i = Just $ concTerm $ - i
  nonConstantHandler (UMinusITerm v) = Just v
  -- nonConstantHandler (MinusITerm l r) = Just $ minusi r l
  nonConstantHandler (AddITerm (IntegerConcTerm l) r) = Just $ minusi (concTerm $ - l) r
  nonConstantHandler (AddITerm (UMinusITerm l) r) = Just $ addi l (uminusi r)
  nonConstantHandler (AddITerm l (UMinusITerm r)) = Just $ addi (uminusi l) r
  nonConstantHandler (TimesITerm (IntegerConcTerm l) r) = Just $ timesi (concTerm $ - l) r
  nonConstantHandler (TimesITerm (UMinusITerm _) _) = error "Should not happen"
  nonConstantHandler (TimesITerm _ (UMinusITerm _)) = error "Should not happen"
  nonConstantHandler (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ minusi (concTerm $ -r) l
  nonConstantHandler _ = Nothing

instance UnaryOp UMinusI Integer Integer where
  partialEvalUnary _ v = unaryUnfoldOnce (unaryPartial @UMinusI) (constructUnary UMinusI) v
  pformatUnary v = "(-I " ++ pformat v ++ ")"

pattern UMinusITerm :: Term Integer -> Term a
pattern UMinusITerm v <- UnaryTermPatt UMinusI v

-- lt
data LTI = LTI deriving (Show)

lti :: Term Integer -> Term Integer -> Term Bool
lti = partialEvalBinary LTI

instance BinaryPartialStrategy LTI Integer Integer Bool where
  extractora = integerConcTermView
  extractorb = integerConcTermView
  allConstantHandler l r = Just $ concTerm $ l < r
  leftConstantHandler l (AddITerm (IntegerConcTerm j) k) = Just $ lti (concTerm $ l - j) k
  -- leftConstantHandler l (UMinusITerm j) = Just $ lti j $ concTerm $ -l
  leftConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ lti (concTerm $ l - k) j
  leftConstantHandler _ _ = Nothing
  rightConstantHandler (AddITerm (IntegerConcTerm i) j) k = Just $ lti j (concTerm $ k - i)
  rightConstantHandler (UMinusITerm i) j = Just $ lti (concTerm $ - j) i
  rightConstantHandler (AddITerm _ (IntegerConcTerm _)) _ = error "Should not happen" -- Just $ lti i (concTerm $ k - j)
  rightConstantHandler l r = Just $ lti (concTerm $ - r) (uminusi l)

  nonBinaryConstantHandler (AddITerm (IntegerConcTerm j) k) l = Just $ lti (concTerm j) (minusi k l)
  nonBinaryConstantHandler j (AddITerm (IntegerConcTerm k) l) = Just $ lti (concTerm $ - k) (minusi l j)
  nonBinaryConstantHandler (AddITerm _ (IntegerConcTerm _)) _ = error "Should not happen" -- Just $ lti (concTerm k) (minusi j l)
  nonBinaryConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ lti (concTerm $ -l) (minusi k j)
  nonBinaryConstantHandler _ _ = Nothing

instance BinaryOp LTI Integer Integer Bool where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @LTI) (constructBinary LTI) l r
  pformatBinary l r = "(<I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern LTITerm :: Term Integer -> Term Integer -> Term a
pattern LTITerm l r <- BinaryTermPatt LTI l r

-- le
data LEI = LEI deriving (Show)

lei :: Term Integer -> Term Integer -> Term Bool
lei = partialEvalBinary LEI

instance BinaryPartialStrategy LEI Integer Integer Bool where
  extractora = integerConcTermView
  extractorb = integerConcTermView
  allConstantHandler l r = Just $ concTerm $ l <= r
  leftConstantHandler l (AddITerm (IntegerConcTerm j) k) = Just $ lei (concTerm $ l - j) k
  leftConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ lti (concTerm $ l - k) j
  leftConstantHandler _ _ = Nothing
  rightConstantHandler (AddITerm (IntegerConcTerm i) j) k = Just $ lei j (concTerm $ k - i)
  rightConstantHandler (UMinusITerm i) j = Just $ lei (concTerm $ - j) i
  rightConstantHandler (AddITerm _ (IntegerConcTerm _)) _ = error "Should not happen" -- Just $ lti i (concTerm $ k - j)
  rightConstantHandler l r = Just $ lei (concTerm $ - r) (uminusi l)

  nonBinaryConstantHandler (AddITerm (IntegerConcTerm j) k) l = Just $ lei (concTerm j) (minusi k l)
  nonBinaryConstantHandler j (AddITerm (IntegerConcTerm k) l) = Just $ lei (concTerm $ - k) (minusi l j)
  nonBinaryConstantHandler (AddITerm _ (IntegerConcTerm _)) _ = error "Should not happen" -- Just $ lti (concTerm k) (minusi j l)
  nonBinaryConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ lti (concTerm $ -l) (minusi k j)
  nonBinaryConstantHandler _ _ = Nothing

instance BinaryOp LEI Integer Integer Bool where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @LEI) (constructBinary LEI) l r
  pformatBinary l r = "(<=I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern LEITerm :: Term Integer -> Term Integer -> Term a
pattern LEITerm l r <- BinaryTermPatt LEI l r

gti :: Term Integer -> Term Integer -> Term Bool
gti = flip lei

gei :: Term Integer -> Term Integer -> Term Bool
gei = flip lti

-- times
data TimesI = TimesI deriving (Show)

timesi :: Term Integer -> Term Integer -> Term Integer
timesi = partialEvalBinary TimesI

instance BinaryCommPartialStrategy TimesI Integer Integer where
  singleConstantHandler 0 _ = Just $ concTerm 0
  singleConstantHandler 1 k = Just k
  singleConstantHandler (-1) k = Just $ uminusi k
  singleConstantHandler l (TimesITerm (IntegerConcTerm j) k) = Just $ timesi (concTerm $ l * j) k
  singleConstantHandler l (AddITerm (IntegerConcTerm j) k) = Just $ addi (concTerm $ l * j) (timesi (concTerm l) k)
  singleConstantHandler l (UMinusITerm j) = Just (timesi (concTerm $ - l) j)
  singleConstantHandler _ (TimesITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ addi (concTerm $ l + k) j
  singleConstantHandler _ (AddITerm _ (IntegerConcTerm _)) = error "Should not happen"
  singleConstantHandler _ _ = Nothing

instance BinaryPartialStrategy TimesI Integer Integer Integer where
  extractora = integerConcTermView
  extractorb = integerConcTermView
  allConstantHandler i j = Just $ concTerm $ i * j

  nonBinaryConstantHandler (TimesITerm i@(IntegerConcTerm _) j) k = Just $ timesi i $ timesi j k
  nonBinaryConstantHandler i (TimesITerm j@(IntegerConcTerm _) k) = Just $ timesi j $ timesi i k
  nonBinaryConstantHandler (UMinusITerm i) j = Just $ uminusi $ timesi i j
  nonBinaryConstantHandler i (UMinusITerm j) = Just $ uminusi $ timesi i j
  nonBinaryConstantHandler i j@(IntegerConcTerm _) = Just $ timesi j i
  nonBinaryConstantHandler (TimesITerm _ (IntegerConcTerm _)) _ = error "Should not happen" -- Just $ addi j $ addi i k
  nonBinaryConstantHandler _ (TimesITerm _ (IntegerConcTerm _)) = error "Should not happen" -- Just $ addi k $ addi i j
  nonBinaryConstantHandler _ _ = Nothing

instance BinaryOp TimesI Integer Integer Integer where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @TimesI) (constructBinary TimesI) l r
  pformatBinary l r = "(*I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern TimesITerm :: Term Integer -> Term Integer -> Term a
pattern TimesITerm l r <- BinaryTermPatt TimesI l r

-- div
data DivI = DivI deriving (Show)

divi :: Term Integer -> Term Integer -> Term Integer
divi = partialEvalBinary DivI

instance BinaryPartialStrategy DivI Integer Integer Integer where
  extractora = integerConcTermView
  extractorb = integerConcTermView
  allConstantHandler i j
    | j /= 0 = Just $ concTerm $ i `div` j
  allConstantHandler _ _ = Nothing
  leftConstantHandler _ _ = Nothing
  rightConstantHandler i 1 = Just i
  rightConstantHandler _ _ = Nothing
  nonBinaryConstantHandler _ _ = Nothing

instance BinaryOp DivI Integer Integer Integer where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @DivI) (constructBinary DivI) l r
  pformatBinary l r = "(/I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern DivITerm :: Term Integer -> Term Integer -> Term a
pattern DivITerm l r <- BinaryTermPatt DivI l r

-- mod
data ModI = ModI deriving (Show)

modi :: Term Integer -> Term Integer -> Term Integer
modi = partialEvalBinary ModI

instance BinaryPartialStrategy ModI Integer Integer Integer where
  extractora = integerConcTermView
  extractorb = integerConcTermView
  allConstantHandler i j
    | j /= 0 = Just $ concTerm $ i `mod` j
  allConstantHandler _ _ = Nothing
  leftConstantHandler _ _ = Nothing
  rightConstantHandler i 1 = Just i
  rightConstantHandler _ _ = Nothing
  nonBinaryConstantHandler _ _ = Nothing

instance BinaryOp ModI Integer Integer Integer where
  partialEvalBinary _ l r = binaryUnfoldOnce (binaryPartial @ModI) (constructBinary ModI) l r
  pformatBinary l r = "(%I " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern ModITerm :: Term Integer -> Term Integer -> Term a
pattern ModITerm l r <- BinaryTermPatt ModI l r
