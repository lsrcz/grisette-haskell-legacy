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

newtype MemoHashMap k v = MemoHashMap {unMemoHashMap :: M.HashMap k v}

emptyMemoHashMap :: MemoHashMap k v
emptyMemoHashMap = MemoHashMap {unMemoHashMap = M.empty}

instance (Eq a, Hashable a) => MapLike (MemoHashMap a b) a b where
  lookup k = M.lookup k . unMemoHashMap
  add k v = MemoHashMap . M.insert k v . unMemoHashMap

enum' :: (HasTrie a) => (a -> a') -> (a :->: b) -> [(a', b)]
enum' f = (fmap . first) f . enumerate

instance HasTrie B.ByteString where
  newtype (B.ByteString :->: x) = ByteStringTrie (String :->: x)
  trie f = ByteStringTrie $ trie (f . C.pack)
  untrie (ByteStringTrie t) = untrie t . C.unpack
  enumerate (ByteStringTrie t) = enum' C.pack t

type HashTable k v = H.BasicHashTable k v

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

htmup :: (Eq k, Hashable k) => (b -> c) -> (k -> b) -> (k -> c)
htmup mem f = htmemo (mem . f)

htmemo2 :: (Eq k1, Hashable k1, Eq k2, Hashable k2) => (k1 -> k2 -> a) -> (k1 -> k2 -> a)
htmemo2 = htmup htmemo

htmemo3 :: (Eq k1, Hashable k1, Eq k2, Hashable k2, Eq k3, Hashable k3) =>
  (k1 -> k2 -> k3 -> a) -> (k1 -> k2 -> k3 -> a)
htmemo3 = htmup htmemo2

htmemoFix :: (Eq k, Hashable k) => ((k -> a) -> (k -> a)) -> k -> a
htmemoFix h = fix (htmemo . h)
