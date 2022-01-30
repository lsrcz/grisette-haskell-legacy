{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.BV
  ( pattern SignedBVConcTerm,
    pattern SignedBVTerm,
    pattern UnsignedBVConcTerm,
    pattern UnsignedBVTerm,
  )
where

import Data.BitVector.Sized.Signed as BVS
import Data.BitVector.Sized.Unsigned as BVU
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

unsignedBVConcTermView :: forall w a. (KnownNat w) => Term a -> Maybe (UnsignedBV w)
unsignedBVConcTermView (ConcTerm _ b) = cast b
unsignedBVConcTermView _ = Nothing

pattern UnsignedBVConcTerm :: forall w a. (KnownNat w) => UnsignedBV w -> Term a
pattern UnsignedBVConcTerm b <- (unsignedBVConcTermView -> Just b)

unsignedBVTermView :: forall w a. (KnownNat w) => Term a -> Maybe (Term (UnsignedBV w))
unsignedBVTermView = castTerm

pattern UnsignedBVTerm :: (KnownNat w) => Term (UnsignedBV w) -> Term a
pattern UnsignedBVTerm b <- (unsignedBVTermView -> Just b)
