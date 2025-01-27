{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Grisette.IR.SymPrim.Data.BV where

import Control.DeepSeq
import Data.Bits
import Data.Hashable
import Data.Proxy
import GHC.Generics
import GHC.TypeNats
import Grisette.Core.Data.Class.BitVector
import Language.Haskell.TH.Syntax
import Numeric

newtype WordN (n :: Nat) = WordN {unWordN :: Integer}
  deriving (Eq, Ord, Generic, Lift, Hashable, NFData)

instance (KnownNat n, 1 <= n) => Show (WordN n) where
  show (WordN w) = if (bitwidth `mod` 4) == 0 then hexRepPre ++ hexRep else binRepPre ++ binRep
    where
      bitwidth = natVal (Proxy :: Proxy n)
      hexRepPre = "0x" ++ replicate (fromIntegral (bitwidth `div` 4) - length hexRep) '0'
      hexRep = showHex w ""
      binRepPre = "0b" ++ replicate (fromIntegral bitwidth - length binRep) '0'
      binRep = showIntAtBase 2 (\x -> if x == 0 then '0' else '1') w ""

newtype IntN (n :: Nat) = IntN {unIntN :: Integer}
  deriving (Eq, Generic, Lift, Hashable, NFData)

instance (KnownNat n, 1 <= n) => Show (IntN n) where
  show (IntN w) = if (bitwidth `mod` 4) == 0 then hexRepPre ++ hexRep else binRepPre ++ binRep
    where
      bitwidth = natVal (Proxy :: Proxy n)
      hexRepPre = "0x" ++ replicate (fromIntegral (bitwidth `div` 4) - length hexRep) '0'
      hexRep = showHex w ""
      binRepPre = "0b" ++ replicate (fromIntegral bitwidth - length binRep) '0'
      binRep = showIntAtBase 2 (\x -> if x == 0 then '0' else '1') w ""

maxWordN :: forall proxy n. KnownNat n => proxy n -> WordN n
maxWordN _ = WordN ((1 `shiftL` fromIntegral (natVal (Proxy :: Proxy n))) - 1)

instance (KnownNat n, 1 <= n) => Bits (WordN n) where
  WordN a .&. WordN b = WordN (a .&. b)
  WordN a .|. WordN b = WordN (a .|. b)
  WordN a `xor` WordN b = WordN (a `xor` b)
  complement a = maxWordN (Proxy :: Proxy n) `xor` a

  -- shift use default implementation
  -- rotate use default implementation
  zeroBits = WordN 0
  bit i
    | i < 0 || i >= fromIntegral (natVal (Proxy :: Proxy n)) = zeroBits
    | otherwise = WordN (bit i)

  -- setBit use default implementation
  clearBit (WordN a) i = WordN (clearBit a i)

  -- complementBit use default implementation
  testBit (WordN a) i = testBit a i
  bitSizeMaybe _ = Just $ fromIntegral (natVal (Proxy :: Proxy n))
  bitSize _ = fromIntegral (natVal (Proxy :: Proxy n))
  isSigned _ = False
  shiftL (WordN a) i = WordN (a `shiftL` i) .&. maxWordN (Proxy :: Proxy n)

  -- unsafeShiftL use default implementation
  shiftR (WordN a) i = WordN (a `shiftR` i)

  -- unsafeShiftR use default implementation
  rotateL a 0 = a
  rotateL (WordN a) k
    | k >= n = rotateL (WordN a) (k `mod` n)
    | otherwise = WordN $ l + h
    where
      n = fromIntegral $ natVal (Proxy :: Proxy n)
      s = n - k
      l = a `shiftR` s
      h = (a - (l `shiftL` s)) `shiftL` k
  rotateR a 0 = a
  rotateR (WordN a) k
    | k >= n = rotateR (WordN a) (k `mod` n)
    | otherwise = WordN $ l + h
    where
      n = fromIntegral $ natVal (Proxy :: Proxy n)
      s = n - k
      l = a `shiftR` k
      h = (a - (l `shiftL` k)) `shiftL` s
  popCount (WordN n) = popCount n

instance (KnownNat n, 1 <= n) => Num (WordN n) where
  WordN x + WordN y = WordN (x + y) .&. maxWordN (Proxy :: Proxy n)
  WordN x * WordN y = WordN (x * y) .&. maxWordN (Proxy :: Proxy n)
  WordN x - WordN y
    | x >= y = WordN (x - y)
    | otherwise = WordN ((1 `shiftL` fromIntegral (natVal (Proxy :: Proxy n))) + x - y)
  negate (WordN 0) = WordN 0
  negate a = complement a + WordN 1
  abs x = x
  signum (WordN 0) = 0
  signum _ = 1
  fromInteger !x
    | x == 0 = WordN 0
    | x > 0 = WordN (x .&. unWordN (maxWordN (Proxy :: Proxy n)))
    | otherwise = -fromInteger (-x)

minusOneIntN :: forall proxy n. KnownNat n => proxy n -> IntN n
minusOneIntN _ = IntN (1 `shiftL` fromIntegral (natVal (Proxy :: Proxy n)) - 1)

instance (KnownNat n, 1 <= n) => Bits (IntN n) where
  IntN a .&. IntN b = IntN (a .&. b)
  IntN a .|. IntN b = IntN (a .|. b)
  IntN a `xor` IntN b = IntN (a `xor` b)
  complement a = minusOneIntN (Proxy :: Proxy n) `xor` a

  -- shift use default implementation
  -- rotate use default implementation
  zeroBits = IntN 0
  bit i = IntN (unWordN (bit i :: WordN n))

  -- setBit use default implementation
  clearBit (IntN a) i = IntN (clearBit a i)

  -- complementBit use default implementation
  testBit (IntN a) i = testBit a i
  bitSizeMaybe _ = Just $ fromIntegral (natVal (Proxy :: Proxy n))
  bitSize _ = fromIntegral (natVal (Proxy :: Proxy n))
  isSigned _ = True

  shiftL (IntN a) i = IntN (unWordN $ (WordN a :: WordN n) `shiftL` i)

  -- unsafeShiftL use default implementation
  shiftR i 0 = i
  shiftR (IntN i) k
    | k >= n = if b then IntN (maxi - 1) else IntN 0
    | otherwise = if b then IntN (maxi - noi + (i `shiftR` k)) else IntN (i `shiftR` k)
    where
      b = testBit i (n - 1)
      n = fromIntegral $ natVal (Proxy :: Proxy n)
      maxi = (1 :: Integer) `shiftL` n
      noi = (1 :: Integer) `shiftL` (n - k)

  -- unsafeShiftR use default implementation
  rotateL (IntN i) k = IntN $ unWordN $ rotateL (WordN i :: WordN n) k
  rotateR (IntN i) k = IntN $ unWordN $ rotateR (WordN i :: WordN n) k
  popCount (IntN i) = popCount i

instance (KnownNat n, 1 <= n) => Num (IntN n) where
  IntN x + IntN y = IntN (x + y) .&. minusOneIntN (Proxy :: Proxy n)
  IntN x * IntN y = IntN (x * y) .&. minusOneIntN (Proxy :: Proxy n)
  IntN x - IntN y
    | x >= y = IntN (x - y)
    | otherwise = IntN ((1 `shiftL` fromIntegral (natVal (Proxy :: Proxy n))) + x - y)
  negate (IntN 0) = IntN 0
  negate a = complement a + IntN 1
  abs x = if testBit x (fromIntegral $ natVal (Proxy :: Proxy n) - 1) then negate x else x
  signum (IntN 0) = IntN 0
  signum i = if testBit i (fromIntegral $ natVal (Proxy :: Proxy n) - 1) then -1 else 1
  fromInteger !x = IntN $ if v >= 0 then v else (1 `shiftL` n) + v
    where
      v = unWordN (fromInteger (x + maxn) :: WordN n) - maxn
      n = fromIntegral (natVal (Proxy :: Proxy n))
      maxn = 1 `shiftL` (n - 1) - 1

instance (KnownNat n, 1 <= n) => Ord (IntN n) where
  IntN a <= IntN b
    | as && not bs = True
    | not as && bs = False
    | otherwise = a <= b
    where
      n = fromIntegral (natVal (Proxy :: Proxy n))
      as = testBit a (n - 1)
      bs = testBit b (n - 1)

instance
  (KnownNat n, 1 <= n, KnownNat m, 1 <= m, KnownNat w, 1 <= w, w ~ (n + m)) =>
  BVConcat (WordN n) (WordN m) (WordN w)
  where
  bvconcat (WordN a) (WordN b) = WordN ((a `shiftL` fromIntegral (natVal (Proxy :: Proxy m))) .|. b)

instance
  (KnownNat n, 1 <= n, KnownNat m, 1 <= m, KnownNat w, 1 <= w, w ~ (n + m)) =>
  BVConcat (IntN n) (IntN m) (IntN w)
  where
  bvconcat (IntN a) (IntN b) = IntN $ unWordN $ bvconcat (WordN a :: WordN n) (WordN b :: WordN m)

instance (KnownNat n, 1 <= n, KnownNat r, n <= r) => BVExtend (WordN n) r (WordN r) where
  bvzeroExtend _ (WordN v) = WordN v
  bvsignExtend pr (WordN v) = if s then WordN (maxi - noi + v) else WordN v
    where
      r = fromIntegral $ natVal pr
      n = fromIntegral $ natVal (Proxy :: Proxy n)
      s = testBit v (n - 1)
      maxi = (1 :: Integer) `shiftL` r
      noi = (1 :: Integer) `shiftL` n
  bvextend = bvzeroExtend

instance (KnownNat n, 1 <= n, KnownNat r, n <= r) => BVExtend (IntN n) r (IntN r) where
  bvzeroExtend _ (IntN v) = IntN v
  bvsignExtend pr (IntN v) = IntN $ unWordN $ bvsignExtend pr (WordN v :: WordN n)
  bvextend = bvsignExtend

instance (KnownNat n, 1 <= n, KnownNat ix, KnownNat w, 1 <= w, ix + w <= n) => BVSelect (WordN n) ix w (WordN w) where
  bvselect pix pw (WordN v) = WordN ((v `shiftR` ix) .&. mask)
    where
      ix = fromIntegral $ natVal pix
      w = fromIntegral $ natVal pw
      mask = (1 `shiftL` w) - 1

instance (KnownNat n, 1 <= n, KnownNat ix, KnownNat w, 1 <= w, ix + w <= n) => BVSelect (IntN n) ix w (IntN w) where
  bvselect pix pw (IntN v) = IntN $ unWordN $ bvselect pix pw (WordN v :: WordN n)
