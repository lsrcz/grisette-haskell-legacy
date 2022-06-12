{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.IR.SymPrim.Data.Prim.Utils (pattern Dyn) where

import Data.Typeable

pattern Dyn :: (Typeable a, Typeable b) => a -> b
pattern Dyn x <- (cast -> Just x)
