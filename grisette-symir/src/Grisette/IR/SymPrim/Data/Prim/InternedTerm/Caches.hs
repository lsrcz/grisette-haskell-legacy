{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.Caches where

import Data.Data
import Data.Interned
import GHC.IO
import GHC.Base (Any)
import Unsafe.Coerce
import Control.Once
import Data.IORef
import qualified Data.HashMap.Strict as M

termCacheCell :: IO (IORef (M.HashMap TypeRep Any))
termCacheCell = unsafeDupablePerformIO $ once $ newIORef M.empty

typeMemoizedCache :: forall a. (Interned a, Typeable a) => Cache a
typeMemoizedCache = unsafeDupablePerformIO $ do
  c <- termCacheCell
  atomicModifyIORef' c $ \m ->
    case M.lookup (typeRep (Proxy @a)) m of
      Just d -> (m, unsafeCoerce d)
      Nothing -> (M.insert (typeRep (Proxy @a)) (unsafeCoerce r1) m, r1)
        where
            r1 :: Cache a
            !r1 = mkCache
            {-# NOINLINE r1 #-}
        