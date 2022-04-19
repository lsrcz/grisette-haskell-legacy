{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Data.MemoUtils
  ( MemoHashMap (..),
    emptyMemoHashMap,
    enum',
    htmemo,
    htmemo2,
    htmemo3,
    htmup,
    htmemoFix,
  )
where

import Control.Monad.Memo
import qualified Data.HashMap.Lazy as M
import Data.Hashable
import Data.MemoTrie
import Data.Bifunctor
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.HashTable.IO as H
import System.IO.Unsafe
import Data.Function (fix)

-- | A wrapper for 'M.HashMap' for memoization.
newtype MemoHashMap k v = MemoHashMap {unMemoHashMap :: M.HashMap k v}

-- | An empty 'MemoHashMap'
emptyMemoHashMap :: MemoHashMap k v
emptyMemoHashMap = MemoHashMap {unMemoHashMap = M.empty}

instance (Eq a, Hashable a) => MapLike (MemoHashMap a b) a b where
  lookup k = M.lookup k . unMemoHashMap
  add k v = MemoHashMap . M.insert k v . unMemoHashMap

-- | Helper for creating 'enumerate' function for 'HasTrie' instances
enum' :: (HasTrie a) => (a -> a') -> (a :->: b) -> [(a', b)]
enum' f = (fmap . first) f . enumerate

instance HasTrie B.ByteString where
  newtype (B.ByteString :->: x) = ByteStringTrie (String :->: x)
  trie f = ByteStringTrie $ trie (f . C.pack)
  untrie (ByteStringTrie t) = untrie t . C.unpack
  enumerate (ByteStringTrie t) = enum' C.pack t

type HashTable k v = H.BasicHashTable k v

-- | Function memoizer with mutable hash table.
htmemo :: (Eq k, Hashable k) => (k -> a) -> k -> a
htmemo f = unsafePerformIO $ do
                cache <- H.new :: IO (HashTable k v)
                return $ \x -> unsafePerformIO $ do
                    tryV <- H.lookup cache x
                    case tryV of
                        Nothing -> do
                            -- traceM "New value"
                            let v = f x
                            H.insert cache x v
                            return v
                        Just v -> return v

-- | Lift a memoizer to work with one more argument.
htmup :: (Eq k, Hashable k) => (b -> c) -> (k -> b) -> (k -> c)
htmup mem f = htmemo (mem . f)

-- | Function memoizer with mutable hash table. Works on binary functions.
htmemo2 :: (Eq k1, Hashable k1, Eq k2, Hashable k2) => (k1 -> k2 -> a) -> (k1 -> k2 -> a)
htmemo2 = htmup htmemo

-- | Function memoizer with mutable hash table. Works on ternery functions.
htmemo3 :: (Eq k1, Hashable k1, Eq k2, Hashable k2, Eq k3, Hashable k3) =>
  (k1 -> k2 -> k3 -> a) -> (k1 -> k2 -> k3 -> a)
htmemo3 = htmup htmemo2

-- | Memoizing recursion. Use like 'fix'.
htmemoFix :: (Eq k, Hashable k) => ((k -> a) -> (k -> a)) -> k -> a
htmemoFix h = fix (htmemo . h)
