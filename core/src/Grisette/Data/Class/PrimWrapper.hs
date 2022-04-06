{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Class.PrimWrapper
  ( PrimWrapper (..),
    pattern Conc,
  )
where

-- | The class establish the link between concrete primitive types
-- and symbolic primitive types.
class PrimWrapper t c | t -> c where
  -- | Wrap a concrete value in a symbolic value.
  conc :: c -> t
  -- | Extract the concrete value from a symbolic value.
  concView :: t -> Maybe c
  -- | Generate simply-named symbolic variables.
  ssymb :: String -> t
  -- | Generate indexed symbolic variables.
  isymb :: Int -> String -> t

-- | Extract the concrete value from a symbolic value with 'concView'.
pattern Conc :: PrimWrapper t c => c -> t
pattern Conc c <-
  (concView -> Just c)
  where
    Conc c = conc c
