module Grisette.Data.MemoUtils
  ( MemoHashMap (..),
    emptyMemoHashMap,
  )
where

import Control.Monad.Memo
import qualified Data.HashMap.Lazy as M
import Data.Hashable

newtype MemoHashMap k v = MemoHashMap {unMemoHashMap :: M.HashMap k v}

emptyMemoHashMap :: MemoHashMap k v
emptyMemoHashMap = MemoHashMap {unMemoHashMap = M.empty}

instance (Eq a, Hashable a) => MapLike (MemoHashMap a b) a b where
  lookup k = M.lookup k . unMemoHashMap
  add k v = MemoHashMap . M.insert k v . unMemoHashMap
