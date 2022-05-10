{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Grisette.Data.SMT.Config
  ( GrisetteSMTConfig (..),
    sbvConfig,
    TermTy,
  )
where

import Data.BitVector.Sized.Signed
import Data.BitVector.Sized.Unsigned
import qualified Data.SBV as SBV
import GHC.TypeNats
import Grisette.Data.TabularFunc
import Grisette.Data.GeneralFunc
import Data.Kind

type Aux :: Bool -> Nat -> Type
type family Aux o n where
  Aux 'True n = SBV.SInteger
  Aux 'False n = SBV.SInt n

type IsZero :: Nat -> Bool
type family IsZero n where
  IsZero 0 = 'True
  IsZero _ = 'False

type TermTy :: Nat -> Type -> Type
type family TermTy bitWidth b where
  TermTy _ Bool = SBV.SBool
  TermTy n Integer = Aux (IsZero n) n
  TermTy n (SignedBV x) = SBV.SBV (SBV.IntN x)
  TermTy n (UnsignedBV x) = SBV.SBV (SBV.WordN x)
  TermTy n (a =-> b) = TermTy n a -> TermTy n b
  TermTy n (a --> b) = TermTy n a -> TermTy n b
  TermTy _ v = v

data GrisetteSMTConfig (integerBitWidth :: Nat) where
  UnboundedReasoning :: SBV.SMTConfig -> GrisetteSMTConfig 0
  BoundedReasoning ::
    (KnownNat integerBitWidth, IsZero integerBitWidth ~ 'False, SBV.BVIsNonZero integerBitWidth) =>
    SBV.SMTConfig ->
    GrisetteSMTConfig integerBitWidth

sbvConfig :: forall integerBitWidth. GrisetteSMTConfig integerBitWidth -> SBV.SMTConfig
sbvConfig (UnboundedReasoning config) = config
sbvConfig (BoundedReasoning config) = config
