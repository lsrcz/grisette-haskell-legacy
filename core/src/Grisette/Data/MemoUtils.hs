{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Data.MemoUtils
  ( MemoHashMap (..),
    emptyMemoHashMap,
    enum'
  )
where

import Control.Monad.Memo
import qualified Data.HashMap.Lazy as M
import Data.Hashable
import Data.MemoTrie
import Data.Bifunctor
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C

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
