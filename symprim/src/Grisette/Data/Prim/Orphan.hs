{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Data.Prim.Orphan where
import GHC.TypeNats
import Data.Hashable
import Data.BitVector.Sized.Signed
import Language.Haskell.TH.Syntax
import Control.DeepSeq
import Data.BitVector.Sized.Unsigned

instance (KnownNat w, 1 <= w) => Hashable (SignedBV w) where
  s `hashWithSalt` (SignedBV b) = s `hashWithSalt` b

deriving instance (Lift (SignedBV v))

deriving instance (NFData (SignedBV v))
instance (KnownNat w, 1 <= w) => Hashable (UnsignedBV w) where
  s `hashWithSalt` (UnsignedBV b) = s `hashWithSalt` b

deriving instance (Lift (UnsignedBV v))

deriving instance (NFData (UnsignedBV v))

