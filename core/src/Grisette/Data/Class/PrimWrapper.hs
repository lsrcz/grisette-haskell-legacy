{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Grisette.Data.Class.PrimWrapper (
  PrimWrapper(..)
) where

class PrimWrapper t c | t -> c where
  conc :: c -> t
  symb :: String -> t
