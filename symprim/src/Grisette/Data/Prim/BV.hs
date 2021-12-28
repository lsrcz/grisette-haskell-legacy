{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.BV
  ( pattern SignedBVConcTerm,
    pattern SignedBVTerm,
  )
where

import Data.BitVector.Sized.Signed
import Data.Typeable
import GHC.TypeNats
import Grisette.Data.Prim.InternedTerm

signedBVConcTermView :: forall w a. (KnownNat w) => Term a -> Maybe (SignedBV w)
signedBVConcTermView (ConcTerm _ b) = cast b
signedBVConcTermView _ = Nothing

pattern SignedBVConcTerm :: forall w a. (KnownNat w) => SignedBV w -> Term a
pattern SignedBVConcTerm b <- (signedBVConcTermView -> Just b)

signedBVTermView :: forall w a. (KnownNat w) => Term a -> Maybe (Term (SignedBV w))
signedBVTermView = castTerm

pattern SignedBVTerm :: (KnownNat w) => Term (SignedBV w) -> Term a
pattern SignedBVTerm b <- (signedBVTermView -> Just b)
