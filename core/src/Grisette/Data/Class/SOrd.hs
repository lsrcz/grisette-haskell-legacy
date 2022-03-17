{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.SOrd
  ( SOrd (..),
    SOrd' (..),
    derivedSymLt,
    derivedSymLe,
    derivedSymGt,
    derivedSymGe,
  )
where

import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper
import qualified Data.ByteString as B
import Grisette.Control.Monad

class (SEq' bool f) => SOrd' bool f where
  (<~~) :: f a -> f a -> bool
  (<=~~) :: f a -> f a -> bool
  (>~~) :: f a -> f a -> bool
  (>=~~) :: f a -> f a -> bool
  infix 4 <~~
  infix 4 <=~~
  infix 4 >~~
  infix 4 >=~~
  symCompare' :: (MonadUnion bool u) => f a -> f a -> u Ordering

instance (SymBoolOp bool) => SOrd' bool U1 where
  _ <~~ _ = conc False
  _ <=~~ _ = conc True
  _ >~~ _ = conc False
  _ >=~~ _ = conc True
  symCompare' _ _ = mrgReturn EQ

instance (SymBoolOp bool) => SOrd' bool V1 where
  _ <~~ _ = conc False
  _ <=~~ _ = conc True
  _ >~~ _ = conc False
  _ >=~~ _ = conc True
  symCompare' _ _ = mrgReturn EQ

instance (SymBoolOp bool, SOrd bool c) => SOrd' bool (K1 i c) where
  (K1 a) <~~ (K1 b) = a <~ b
  (K1 a) <=~~ (K1 b) = a <=~ b
  (K1 a) >~~ (K1 b) = a >~ b
  (K1 a) >=~~ (K1 b) = a >=~ b
  symCompare' (K1 a) (K1 b) = symCompare a b

instance (SymBoolOp bool, SOrd' bool a) => SOrd' bool (M1 i c a) where
  (M1 a) <~~ (M1 b) = a <~~ b
  (M1 a) <=~~ (M1 b) = a <=~~ b
  (M1 a) >~~ (M1 b) = a >~~ b
  (M1 a) >=~~ (M1 b) = a >=~~ b
  symCompare' (M1 a) (M1 b) = symCompare' a b

instance (SymBoolOp bool, SOrd' bool a, SOrd' bool b) => SOrd' bool (a :+: b) where
  (L1 _) <~~ (R1 _) = conc True
  (L1 a) <~~ (L1 b) = a <~~ b
  (R1 _) <~~ (L1 _) = conc False
  (R1 a) <~~ (R1 b) = a <~~ b
  (L1 _) <=~~ (R1 _) = conc True
  (L1 a) <=~~ (L1 b) = a <=~~ b
  (R1 _) <=~~ (L1 _) = conc False
  (R1 a) <=~~ (R1 b) = a <=~~ b

  (L1 _) >~~ (R1 _) = conc False
  (L1 a) >~~ (L1 b) = a >~~ b
  (R1 _) >~~ (L1 _) = conc True
  (R1 a) >~~ (R1 b) = a >~~ b
  (L1 _) >=~~ (R1 _) = conc False
  (L1 a) >=~~ (L1 b) = a >=~~ b
  (R1 _) >=~~ (L1 _) = conc True
  (R1 a) >=~~ (R1 b) = a >=~~ b

  symCompare' (L1 a) (L1 b) = symCompare' a b
  symCompare' (L1 _) (R1 _) = mrgReturn LT
  symCompare' (R1 a) (R1 b) = symCompare' a b
  symCompare' (R1 _) (L1 _) = mrgReturn GT

instance (SymBoolOp bool, SOrd' bool a, SOrd' bool b) => SOrd' bool (a :*: b) where
  (a1 :*: b1) <~~ (a2 :*: b2) = (a1 <~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 <~~ b2))
  (a1 :*: b1) <=~~ (a2 :*: b2) = (a1 <~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 <=~~ b2))
  (a1 :*: b1) >~~ (a2 :*: b2) = (a1 >~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 >~~ b2))
  (a1 :*: b1) >=~~ (a2 :*: b2) = (a1 >~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 >=~~ b2))
  symCompare' (a1 :*: b1) (a2 :*: b2) = do
    l <- symCompare' a1 a2
    case l of
      EQ -> symCompare' b1 b2
      _ -> mrgReturn l

derivedSymLt :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymLt x y = from x <~~ from y

derivedSymLe :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymLe x y = from x <=~~ from y

derivedSymGt :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymGt x y = from x >~~ from y

derivedSymGe :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymGe x y = from x >=~~ from y

derivedSymCompare :: (Generic a, SOrd' bool (Rep a), MonadUnion bool u) => a -> a -> u Ordering
derivedSymCompare x y = symCompare' (from x) (from y)

class (SEq bool a) => SOrd bool a where
  (<~) :: a -> a -> bool
  (<=~) :: a -> a -> bool
  (>~) :: a -> a -> bool
  (>=~) :: a -> a -> bool
  infix 4 <~
  infix 4 <=~
  infix 4 >~
  infix 4 >=~
  x <~ y = x <=~ y &&~ x /=~ y
  x >~ y = y <~ x
  x >=~ y = y <=~ x
  symCompare :: (MonadUnion bool u) => a -> a -> u Ordering
  symCompare l r =
    mrgIf (l <~ r :: bool) (mrgReturn LT)
      (mrgIf (l ==~ r :: bool) (mrgReturn EQ) (mrgReturn GT))
  {-# MINIMAL (<=~) #-}
  
instance (SymBoolOp bool) => SOrd bool Bool where
  l <=~ r = conc $ l <= r
  l <~ r = conc $ l < r
  l >=~ r = conc $ l >= r
  l >~ r = conc $ l > r
  symCompare l r = mrgReturn $ compare l r

instance (SymBoolOp bool) => SOrd bool Integer where
  l <=~ r = conc $ l <= r
  l <~ r = conc $ l < r
  l >=~ r = conc $ l >= r
  l >~ r = conc $ l > r
  symCompare l r = mrgReturn $ compare l r

instance (SymBoolOp bool) => SOrd bool Char where
  l <=~ r = conc $ l <= r
  l <~ r = conc $ l < r
  l >=~ r = conc $ l >= r
  l >~ r = conc $ l > r
  symCompare l r = mrgReturn $ compare l r

symCompareSingleList :: (SymBoolOp bool, SOrd bool a) => Bool -> Bool -> [a] -> [a] -> bool
symCompareSingleList isLess isStrict = go
  where
    go [] [] = conc (not isStrict)
    go (x:xs) (y:ys) = (if isLess then x <~ y else x >~ y) ||~ (x ==~ y &&~ go xs ys)
    go [] _ = if isLess then conc True else conc False
    go _ [] = if isLess then conc False else conc True

symCompareList :: (SymBoolOp bool, SOrd bool a, MonadUnion bool u) => [a] -> [a] -> u Ordering
symCompareList [] [] = mrgReturn EQ
symCompareList (x:xs) (y:ys) = do
  oxy <- symCompare x y
  case oxy of
    LT -> mrgReturn LT
    EQ -> symCompareList xs ys
    GT -> mrgReturn GT
symCompareList [] _ = mrgReturn LT
symCompareList _ [] = mrgReturn GT

instance (SymBoolOp bool, SOrd bool a) => SOrd bool [a] where
  (<=~) = symCompareSingleList True False
  (<~) = symCompareSingleList True True
  (>=~) = symCompareSingleList False False
  (>~) = symCompareSingleList False True
  symCompare = symCompareList

instance (SymBoolOp bool, SOrd bool a) => SOrd bool (Maybe a) where
  (<=~) = derivedSymLe
  (<~) = derivedSymLt
  (>=~) = derivedSymGe
  (>~) = derivedSymGt
  symCompare = derivedSymCompare

instance (SymBoolOp bool, SOrd bool a, SOrd bool b) => SOrd bool (Either a b) where
  (<=~) = derivedSymLe
  (<~) = derivedSymLt
  (>=~) = derivedSymGe
  (>~) = derivedSymGt
  symCompare = derivedSymCompare

instance (SymBoolOp bool) => SOrd bool () where
  (<=~) = derivedSymLe
  (<~) = derivedSymLt
  (>=~) = derivedSymGe
  (>~) = derivedSymGt
  symCompare = derivedSymCompare

instance (SymBoolOp bool, SOrd bool a, SOrd bool b) => SOrd bool (a, b) where
  (<=~) = derivedSymLe
  (<~) = derivedSymLt
  (>=~) = derivedSymGe
  (>~) = derivedSymGt
  symCompare = derivedSymCompare

instance (SymBoolOp bool) => SOrd bool B.ByteString where
  l <=~ r = conc $ l <= r
  l <~ r = conc $ l < r
  l >=~ r = conc $ l >= r
  l >~ r = conc $ l > r
  symCompare l r = mrgReturn $ compare l r
