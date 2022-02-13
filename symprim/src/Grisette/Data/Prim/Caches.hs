{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -fno-cse #-}
module Grisette.Data.Prim.Caches where
import Data.Interned
import Data.Data
import Data.Dynamic
-- import Data.Array
import qualified Data.HashMap.Strict as M
-- import qualified Data.HashTable.IO as H
import qualified Data.TypeRepMap as TM
import Data.IORef
import GHC.IO
-- import Data.Typeable
-- import Debug.Trace

newDynamicCache :: forall a. (Interned a, Typeable a) => Dynamic
newDynamicCache = toDyn $ mkCache @a

termCacheCell :: IORef (M.HashMap TypeRep Dynamic)
termCacheCell = unsafeDupablePerformIO $ newIORef M.empty
{-# NOINLINE termCacheCell #-}

typeMemoizedCache :: forall a. (Interned a, Typeable a) => Cache a
typeMemoizedCache = unsafeDupablePerformIO $
  atomicModifyIORef' termCacheCell $ \m ->
    case M.lookup (typeRep (Proxy @a)) m of
      Just d -> (m, fromDyn d undefined)
      Nothing -> (M.insert (typeRep (Proxy @a)) r m, fromDyn r undefined)
        where
          !r = (newDynamicCache @a)
{-# NOINLINE typeMemoizedCache #-}

{-
newtype ReverseCache t = ReverseCache (H.BasicHashTable Id t)

mkReverseCache :: TypeRep -> ReverseCache t
mkReverseCache _ = unsafeDupablePerformIO $ do
  x <- H.new
  return $! ReverseCache x
{-# NOINLINE mkReverseCache #-}

findInReverseCache :: Id -> ReverseCache t -> IO (Maybe t)
findInReverseCache !i (ReverseCache tab) = H.lookup tab i

addToReverseCache :: Id -> t -> ReverseCache t -> IO ()
addToReverseCache !i !t (ReverseCache tab) = H.insert tab i t
-}

newtype ReverseCache t = ReverseCache {getReverseCache :: IORef (M.HashMap Id t)}

mkReverseCache :: (Typeable t) => ReverseCache t
mkReverseCache = ReverseCache (unsafeDupablePerformIO $ newIORef M.empty)
{-# NOINLINE mkReverseCache #-}

findInReverseCache :: Id -> ReverseCache t -> IO (Maybe t)
findInReverseCache !i (ReverseCache ref) = do
  r <- readIORef ref
  return $! M.lookup i r

addToReverseCache :: Id -> t -> ReverseCache t -> IO ()
addToReverseCache !i !t (ReverseCache ref) = atomicModifyIORef' ref $ \m ->
  (M.insert i t m, ())

{-
data ReverseCache t = ReverseCache (Array Int (IORef (M.HashMap Id t)))

cw :: Int
cw = 1024

mkReverseCache :: forall t. (Typeable t) => ReverseCache t
mkReverseCache = ReverseCache $ unsafePerformIO $ do print (show (typeRep (Proxy @t))); traverse newIORef $ listArray (0, cw) $ replicate cw M.empty
{-# NOINLINE mkReverseCache #-}


findInReverseCache :: Id -> ReverseCache t -> IO (Maybe t)
findInReverseCache !i (ReverseCache ref) = do
  r <- readIORef (ref ! (i `mod` cw))
  return $! M.lookup i r

addToReverseCache :: Id -> t -> ReverseCache t -> IO ()
addToReverseCache !i !t (ReverseCache ref) = atomicModifyIORef' (ref ! (i `mod` cw)) $ \m ->
  (M.insert i t m, ())
  -}



termReverseCacheCell :: IORef (TM.TypeRepMap ReverseCache)
termReverseCacheCell = unsafeDupablePerformIO $ newIORef TM.empty
{-# NOINLINE termReverseCacheCell #-}

typeMemoizedReverseCache :: forall a. Typeable a => ReverseCache a
typeMemoizedReverseCache = unsafeDupablePerformIO $ do
  atomicModifyIORef' termReverseCacheCell $ \m ->
    case TM.lookup @a m of
      Just d -> (m, d)
      Nothing -> (TM.insert @a r m, r)
        where
          r :: ReverseCache a
          !r = mkReverseCache
          {-# NOINLINE r #-}
{-# NOINLINE typeMemoizedReverseCache #-}

