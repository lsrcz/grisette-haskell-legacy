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

class (SEq' bool f) => SOrd' bool f where
  (<~~) :: f a -> f a -> bool
  (<=~~) :: f a -> f a -> bool
  (>~~) :: f a -> f a -> bool
  (>=~~) :: f a -> f a -> bool
  infix 4 <~~
  infix 4 <=~~
  infix 4 >~~
  infix 4 >=~~

instance (SymBoolOp bool) => SOrd' bool U1 where
  _ <~~ _ = conc False
  _ <=~~ _ = conc True
  _ >~~ _ = conc False
  _ >=~~ _ = conc True

instance (SymBoolOp bool) => SOrd' bool V1 where
  _ <~~ _ = conc False
  _ <=~~ _ = conc True
  _ >~~ _ = conc False
  _ >=~~ _ = conc True

instance (SymBoolOp bool, SOrd bool c) => SOrd' bool (K1 i c) where
  (K1 a) <~~ (K1 b) = a <~ b
  (K1 a) <=~~ (K1 b) = a <=~ b
  (K1 a) >~~ (K1 b) = a >~ b
  (K1 a) >=~~ (K1 b) = a >=~ b

instance (SymBoolOp bool, SOrd' bool a) => SOrd' bool (M1 i c a) where
  (M1 a) <~~ (M1 b) = a <~~ b
  (M1 a) <=~~ (M1 b) = a <=~~ b
  (M1 a) >~~ (M1 b) = a >~~ b
  (M1 a) >=~~ (M1 b) = a >=~~ b

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

instance (SymBoolOp bool, SOrd' bool a, SOrd' bool b) => SOrd' bool (a :*: b) where
  (a1 :*: b1) <~~ (a2 :*: b2) = (a1 <~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 <~~ b2))
  (a1 :*: b1) <=~~ (a2 :*: b2) = (a1 <~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 <=~~ b2))
  (a1 :*: b1) >~~ (a2 :*: b2) = (a1 >~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 >~~ b2))
  (a1 :*: b1) >=~~ (a2 :*: b2) = (a1 >~~ a2) ||~ ((a1 ==~~ a2) &&~ (b1 >=~~ b2))

derivedSymLt :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymLt x y = from x <~~ from y

derivedSymLe :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymLe x y = from x <=~~ from y

derivedSymGt :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymGt x y = from x >~~ from y

derivedSymGe :: (Generic a, SOrd' bool (Rep a)) => a -> a -> bool
derivedSymGe x y = from x >=~~ from y

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

instance (SymBoolOp bool) => SOrd bool Integer where
  l <=~ r = conc $ l < r

instance (SymBoolOp bool) => SOrd bool Char where
  l <=~ r = conc $ l < r
