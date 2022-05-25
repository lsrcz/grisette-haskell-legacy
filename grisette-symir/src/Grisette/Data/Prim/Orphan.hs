{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.Prim.Orphan where

import Control.DeepSeq
import Data.BitVector.Sized.Signed
import Data.BitVector.Sized.Unsigned
import Data.Hashable
import Language.Haskell.TH.Syntax

instance Hashable (SignedBV w) where
  s `hashWithSalt` (SignedBV b) = s `hashWithSalt` b

deriving instance (Lift (SignedBV v))

deriving instance (NFData (SignedBV v))

instance Hashable (UnsignedBV w) where
  s `hashWithSalt` (UnsignedBV b) = s `hashWithSalt` b

deriving instance (Lift (UnsignedBV v))

deriving instance (NFData (UnsignedBV v))
