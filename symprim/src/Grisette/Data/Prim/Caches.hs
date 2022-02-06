{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fno-cse #-}
module Grisette.Data.Prim.Caches where
import Data.Interned
import Data.Data
import Data.Dynamic
import qualified Data.HashMap.Strict as M
import Data.IORef
import GHC.IO

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

newtype ReverseCache t = ReverseCache {getReverseCache :: IORef (M.HashMap Id t)}

mkReverseCache :: (Typeable t) => ReverseCache t
mkReverseCache = ReverseCache (unsafeDupablePerformIO $ newIORef M.empty)
{-# NOINLINE mkReverseCache #-}

newDynamicReverseCache :: forall (a :: *). (Typeable a) => Dynamic
newDynamicReverseCache = toDyn (mkReverseCache :: ReverseCache a)
{-# NOINLINE newDynamicReverseCache #-}

termReverseCacheCell :: IORef (M.HashMap TypeRep Dynamic)
termReverseCacheCell = unsafeDupablePerformIO $ newIORef M.empty
{-# NOINLINE termReverseCacheCell #-}

typeMemoizedReverseCache :: forall a. Typeable a => ReverseCache a
typeMemoizedReverseCache = unsafeDupablePerformIO $ do
  atomicModifyIORef' termReverseCacheCell $ \m ->
    case M.lookup (typeRep (Proxy @a)) m of
      Just d -> (m, fromDyn d undefined)
      Nothing -> (M.insert (typeRep (Proxy @a)) r m, fromDyn r undefined)
        where
          !r = (newDynamicReverseCache @a)
{-# NOINLINE typeMemoizedReverseCache #-}

