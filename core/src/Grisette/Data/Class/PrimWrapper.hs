{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Class.PrimWrapper
  ( PrimWrapper (..),
    pattern Conc,
  )
where

class PrimWrapper t c | t -> c where
  conc :: c -> t
  concView :: t -> Maybe c
  symb :: String -> t

pattern Conc :: PrimWrapper t c => c -> t
pattern Conc c <-
  (concView -> Just c)
  where
    Conc c = conc c
