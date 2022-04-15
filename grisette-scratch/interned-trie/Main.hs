{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Data.MemoTrie
-- import Data.HashMap.Lazy as H
import Data.Word
import Data.Vector
import Data.Bits
import Debug.Trace

newtype W8 = W8 Word8 deriving Show
instance HasTrie W8 where
  newtype W8 :->: x = W8Trie {unW8Trie :: Vector x}
  trie f = W8Trie $ generate 256 (f . W8 . fromIntegral)
  untrie (W8Trie t) = \(W8 w) -> unsafeIndex t $ fromIntegral w
  enumerate (W8Trie t) = [(W8 $ fromIntegral i, unsafeIndex t i) | i <- [0..255]]

data BL = BNil | BCons W8 BL deriving Show
instance HasTrie BL where
  data BL :->: x = BLTrie x (W8 :->: (BL :->: x))
  trie f = BLTrie (f BNil) (trie $ \w8 -> trie $ \bl -> f $ BCons w8 bl)
  untrie (BLTrie x t) = \case
    BNil -> x
    BCons w8 tl -> untrie (untrie t w8) tl
  enumerate (BLTrie x t) = (BNil, x) : [(BCons w8 bl, v) | (w8, tt) <- enumerate t, (bl, v) <- enumerate tt]

newtype M = M Int deriving Show
instance HasTrie M where
  newtype M :->: x = MTrie (BL :->: x)
  trie f = MTrie $ trie (f . unpackM)
  untrie (MTrie t) = untrie t . packM
  enumerate (MTrie t) = [(unpackM i, v) | (i, v) <- enumerate t]

packM :: M -> BL
packM (M i) = go (fromIntegral i) BNil
  where
    mask = 255 :: Word
    go :: Word -> BL -> BL
    go 0 acc = acc
    go x acc = go (x `shiftR` 8) (BCons (W8 $ fromIntegral $ x .&. mask) acc)

unpackM :: BL -> M
unpackM l = M $ fromIntegral $ go l 0
  where
    go :: BL -> Word -> Word
    go BNil acc = acc
    go (BCons (W8 x) tl) acc = go tl ((acc `shiftL` 8) .|. fromIntegral x)

func :: M -> M
func = memo $ \x -> trace "x" x

{-

instance (HasTrie (IB p)) where
  newtype II p :->: x = IIITrie (IB p :->: x)

instance (HasTrie (II p)) where
  newtype II p :->: x = IIITrie (IB p :->: x)

instance (HasTrie (I p)) where
  newtype I p :->: x = IITrie (II p :->: x)
  -}
  {-
  trie = _
  untrie = _
  enumerate = _
  -}


main :: IO ()
main = putStrLn ""