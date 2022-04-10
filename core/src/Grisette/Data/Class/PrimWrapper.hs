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
  --
  -- >>> conc True :: SymBool
  -- true
  conc :: c -> t
  -- | Extract the concrete value from a symbolic value.
  --
  -- >>> concView (conc True :: SymBool)
  -- Just True
  --
  -- >>> concView (ssymb "a" :: SymBool)
  -- Nothing
  concView :: t -> Maybe c
  -- | Generate simply-named symbolic variables.
  --
  -- >>> ssymb "a" :: SymBool
  -- a
  ssymb :: String -> t
  -- | Generate indexed symbolic variables.
  --
  -- >>> isymb 1 "a" :: SymBool
  -- a@1
  isymb :: Int -> String -> t

-- | Extract the concrete value from a symbolic value with 'concView'.
--
-- >>> case conc True :: SymBool of Conc v -> v
-- True
pattern Conc :: PrimWrapper t c => c -> t
pattern Conc c <-
  (concView -> Just c)
  where
    Conc c = conc c
