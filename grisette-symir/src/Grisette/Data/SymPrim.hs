{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.SymPrim
  ( Sym (..),
    --SymConcView (..),
    --pattern SymConc,
    SymBool,
    SymInteger,
    type (=~>),
    type (-~>),
    SymSignedBV,
    SymUnsignedBV,
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.BitVector.Sized (knownNat, pattern BV)
import Data.BitVector.Sized.Signed (SignedBV (..), mkSignedBV)
import Data.BitVector.Sized.Unsigned
import Data.Bits
-- import Data.Char (chr, ord)
import Data.HashSet as S
import Data.Hashable
import Data.Int
import Data.Proxy
import Data.String
import Data.Word
import GHC.Generics
import GHC.TypeLits
import Grisette.Core.Data.Class.BitVector
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Error
import Grisette.Core.Data.Class.Evaluate
import Grisette.Core.Data.Class.ExtractSymbolics
import Grisette.Core.Data.Class.Function
import Grisette.Core.Data.Class.GenSym
import Grisette.Core.Data.Class.Integer
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.PrimWrapper
import Grisette.Core.Data.Class.SOrd
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.Core.Data.Class.ToCon
import Grisette.Core.Data.Class.ToSym
import Grisette.Data.GeneralFunc
import Grisette.Data.Prim.BV
import Grisette.Data.Prim.Bits
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.GeneralFunc
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model
import Grisette.Data.Prim.Num
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.TabularFunc
import Language.Haskell.TH.Syntax
import Grisette.Lib.Control.Monad

newtype Sym a = Sym {underlyingTerm :: Term a} deriving (Lift, Generic)

instance NFData (Sym a) where
  rnf (Sym t) = rnf t

{-
class SupportedPrim a => SymConcView a where
  symConcView :: Sym a -> Maybe a

pattern SymConc :: SymConcView a => a -> Sym a
pattern SymConc c <-
  (Sym (ConcTerm _ c))
  where
    SymConc c = conc c
    -}

instance (SupportedPrim a) => ITEOp (Sym Bool) (Sym a) where
  ites (Sym c) (Sym t) (Sym f) = Sym $ iteterm c t f

instance (SupportedPrim a) => Mergeable (Sym Bool) (Sym a) where
  mergeStrategy = SimpleStrategy ites

instance (SupportedPrim a) => SimpleMergeable (Sym Bool) (Sym a) where
  mrgIte = ites

instance (SupportedPrim a) => PrimWrapper (Sym a) a where
  conc = Sym . concTerm
  ssymb = Sym . ssymbTerm
  isymb i str = Sym $ isymbTerm i str
  sinfosymb str info = Sym $ sinfosymbTerm str info
  iinfosymb i str info = Sym $ iinfosymbTerm i str info
  concView (Sym (ConcTerm _ t)) = Just t
  concView _ = Nothing

instance (SupportedPrim t) => IsString (Sym t) where
  fromString = ssymb

instance (SupportedPrim a) => ToSym (Sym a) (Sym a) where
  toSym = id

instance (SupportedPrim a) => ToSym a (Sym a) where
  toSym = conc

instance (SupportedPrim a) => ToCon (Sym a) (Sym a) where
  toCon = Just

instance (SupportedPrim a) => ToCon (Sym a) a where
  toCon = concView

instance (SupportedPrim a) => Evaluate Model (Sym a) where
  evaluate fillDefault model (Sym t) = Sym $ evaluateTerm fillDefault model t

instance (SupportedPrim a) => ExtractSymbolics (S.HashSet TermSymbol) (Sym a) where
  extractSymbolics (Sym t) = extractSymbolicsTerm t

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSym (Sym Bool) () (Sym a) where
  genSymFresh _ = mrgReturn <$> genSymSimpleFresh @(Sym Bool) ()

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSymSimple (Sym Bool) () (Sym a) where
  genSymSimpleFresh _ = do
    ident <- ask
    idx@(GenSymIndex i) <- get
    put $ idx + 1
    case ident of
      GenSymIdent s -> return $ isymb i s
      GenSymIdentWithInfo s info -> return $ iinfosymb i s info

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSym (Sym Bool) (Sym a) (Sym a)

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSymSimple (Sym Bool) (Sym a) (Sym a) where
  genSymSimpleFresh _ = genSymSimpleFresh @SymBool ()

instance (SupportedPrim a) => Show (Sym a) where
  show (Sym t) = pformat t

instance (SupportedPrim a) => Hashable (Sym a) where
  hashWithSalt s (Sym v) = s `hashWithSalt` v

instance (SupportedPrim a) => Eq (Sym a) where
  (Sym l) == (Sym r) = l == r

#define SEQ_SYM(type) \
instance (SupportedPrim (type)) => SEq (Sym Bool) (Sym (type)) where \
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

#define SORD_SYM(type) \
instance (SupportedPrim (type)) => SOrd (Sym Bool) (Sym (type)) where \
  (Sym a) <=~ (Sym b) = Sym $ withPrim @(type) $ leNum a b; \
  (Sym a) <~ (Sym b) = Sym $ withPrim @(type) $ ltNum a b; \
  (Sym a) >=~ (Sym b) = Sym $ withPrim @(type) $ geNum a b; \
  (Sym a) >~ (Sym b) = Sym $ withPrim @(type) $ gtNum a b; \
  a `symCompare` b = \
    withPrim @(type) $ mrgIf \
      (a <~ b) \
      (mrgReturn LT) \
      (mrgIf (a ==~ b) (mrgReturn EQ) (mrgReturn GT))

SEQ_SYM (Bool)
SEQ_SYM (Integer)
SEQ_SYM (SignedBV n)
SEQ_SYM (UnsignedBV n)
SORD_SYM (Integer)
SORD_SYM (SignedBV n)
SORD_SYM (UnsignedBV n)

-- bool
type SymBool = Sym Bool

instance SOrd (Sym Bool) (Sym Bool) where
  l <=~ r = nots l ||~ r
  l <~ r = nots l &&~ r
  l >=~ r = l ||~ nots r
  l >~ r = l &&~ nots r
  symCompare l r =
    mrgIf
      (nots l &&~ r)
      (mrgReturn LT)
      (mrgIf (l ==~ r) (mrgReturn EQ) (mrgReturn GT))

instance LogicalOp (Sym Bool) where
  (Sym l) ||~ (Sym r) = Sym $ orb l r
  (Sym l) &&~ (Sym r) = Sym $ andb l r
  nots (Sym v) = Sym $ notb v
  (Sym l) `xors` (Sym r) = Sym $ xorb l r
  (Sym l) `implies` (Sym r) = Sym $ implyb l r

instance SymBoolOp (Sym Bool)

-- integer
type SymInteger = Sym Integer

instance Num (Sym Integer) where
  (Sym l) + (Sym r) = Sym $ addNum l r
  (Sym l) - (Sym r) = Sym $ minusNum l r
  (Sym l) * (Sym r) = Sym $ timesNum l r
  negate (Sym v) = Sym $ uminusNum v
  abs (Sym v) = Sym $ absNum v
  signum (Sym v) = Sym $ signumNum v
  fromInteger i = conc i

instance SignedDivMod (Sym Bool) (Sym Integer) where
  divs (Sym l) rs@(Sym r) =
    mrgIf @(Sym Bool)
      (rs ==~ conc 0)
      (throwError $ transformError DivideByZero)
      (mrgReturn $ Sym $ divi l r)
  mods (Sym l) rs@(Sym r) =
    mrgIf @(Sym Bool)
      (rs ==~ conc 0)
      (throwError $ transformError DivideByZero)
      (mrgReturn $ Sym $ modi l r)

instance SymIntegerOp (Sym Bool) (Sym Integer)

-- signed bv
type SymSignedBV n = Sym (SignedBV n)

instance (SupportedPrim (SignedBV n)) => Num (Sym (SignedBV n)) where
  (Sym l) + (Sym r) = Sym $ withPrim @(SignedBV n) $ addNum l r
  (Sym l) - (Sym r) = Sym $ withPrim @(SignedBV n) $ minusNum l r
  (Sym l) * (Sym r) = Sym $ withPrim @(SignedBV n) $ timesNum l r
  negate (Sym v) = Sym $ withPrim @(SignedBV n) $ uminusNum v
  abs (Sym v) = Sym $ withPrim @(SignedBV n) $ absNum v
  signum (Sym v) = Sym $ withPrim @(SignedBV n) $ signumNum v
  fromInteger i = withPrim @(SignedBV n) $ conc $ mkSignedBV knownNat i

instance (SupportedPrim (SignedBV n)) => Bits (Sym (SignedBV n)) where
  Sym l .&. Sym r = Sym $ withPrim @(SignedBV n) $ bitand l r
  Sym l .|. Sym r = Sym $ withPrim @(SignedBV n) $ bitor l r
  Sym l `xor` Sym r = Sym $ withPrim @(SignedBV n) $ bitxor l r
  complement (Sym n) = Sym $ withPrim @(SignedBV n) $ bitneg n
  shift (Sym n) i = Sym $ withPrim @(SignedBV n) $ bitshift n i
  rotate (Sym n) i = Sym $ withPrim @(SignedBV n) $ bitrotate n i
  bitSize _ = fromInteger $ withPrim @(SignedBV n) $ natVal (Proxy @n)
  bitSizeMaybe _ = Just $ fromInteger $ withPrim @(SignedBV n) $ natVal (Proxy @n)
  isSigned _ = True
  testBit (Conc n) = withPrim @(SignedBV n) $ testBit n
  testBit _ = error "You cannot call testBit on symbolic variables"
  bit = withPrim @(SignedBV n) $ conc . bit
  popCount (Conc n) = withPrim @(SignedBV n) $ popCount n
  popCount _ = error "You cannot call popCount on symbolic variables"

instance
  (KnownNat w', KnownNat n, KnownNat w, w' ~ (n + w), 1 <= n, 1 <= w, 1 <= w') =>
  BVConcat (Sym (SignedBV n)) (Sym (SignedBV w)) (Sym (SignedBV w'))
  where
  bvconcat (Sym l) (Sym r) = Sym (bvtconcat l r)

instance
  (KnownNat n, KnownNat w, KnownNat w', n ~ (w' - w), w' ~ (w + n), 1 <= w, 1 <= n, 1 <= w') =>
  BVExtend (Sym (SignedBV w)) w' (Sym (SignedBV w'))
  where
  bvzeroExtend _ (Sym v) = Sym $ bvtext (Proxy @n) False v
  bvsignExtend _ (Sym v) = Sym $ bvtext (Proxy @n) True v
  bvextend = bvsignExtend

instance
  ( KnownNat ix,
    KnownNat w,
    KnownNat ow,
    ix + w <= ow,
    1 <= ow,
    1 <= w
  ) =>
  BVSelect (Sym (SignedBV ow)) ix w (Sym (SignedBV w))
  where
  bvselect pix pw (Sym v) = Sym $ bvtselect pix pw v

#define TOSYM_MACHINE_INTEGER(int, bv) \
instance ToSym (int) (Sym (bv)) where \
  toSym = fromIntegral

#define TOCON_MACHINE_INTEGER(bvw, n, int) \
instance ToCon (Sym (bvw n)) (int) where \
  toCon (Conc (bvw (BV v) :: bvw n)) = Just $ fromIntegral v; \
  toCon _ = Nothing

TOSYM_MACHINE_INTEGER (Int8, SignedBV 8)
TOSYM_MACHINE_INTEGER (Int16, SignedBV 16)
TOSYM_MACHINE_INTEGER (Int32, SignedBV 32)
TOSYM_MACHINE_INTEGER (Int64, SignedBV 64)
TOSYM_MACHINE_INTEGER (Word8, UnsignedBV 8)
TOSYM_MACHINE_INTEGER (Word16, UnsignedBV 16)
TOSYM_MACHINE_INTEGER (Word32, UnsignedBV 32)
TOSYM_MACHINE_INTEGER (Word64, UnsignedBV 64)

TOCON_MACHINE_INTEGER (SignedBV, 8, Int8)
TOCON_MACHINE_INTEGER (SignedBV, 16, Int16)
TOCON_MACHINE_INTEGER (SignedBV, 32, Int32)
TOCON_MACHINE_INTEGER (SignedBV, 64, Int64)
TOCON_MACHINE_INTEGER (UnsignedBV, 8, Word8)
TOCON_MACHINE_INTEGER (UnsignedBV, 16, Word16)
TOCON_MACHINE_INTEGER (UnsignedBV, 32, Word32)
TOCON_MACHINE_INTEGER (UnsignedBV, 64, Word64)

-- unsigned bv
type SymUnsignedBV n = Sym (UnsignedBV n)

instance (SupportedPrim (UnsignedBV n)) => Num (Sym (UnsignedBV n)) where
  (Sym l) + (Sym r) = Sym $ withPrim @(UnsignedBV n) $ addNum l r
  (Sym l) - (Sym r) = Sym $ withPrim @(UnsignedBV n) $ minusNum l r
  (Sym l) * (Sym r) = Sym $ withPrim @(UnsignedBV n) $ timesNum l r
  negate (Sym v) = Sym $ withPrim @(UnsignedBV n) $ uminusNum v
  abs (Sym v) = Sym $ withPrim @(UnsignedBV n) $ absNum v
  signum (Sym v) = Sym $ withPrim @(UnsignedBV n) $ signumNum v
  fromInteger i = withPrim @(UnsignedBV n) $ conc $ mkUnsignedBV knownNat i

instance
  (KnownNat w', KnownNat n, KnownNat w, w' ~ (n + w), 1 <= n, 1 <= w, 1 <= w') =>
  BVConcat (Sym (UnsignedBV n)) (Sym (UnsignedBV w)) (Sym (UnsignedBV w'))
  where
  bvconcat (Sym l) (Sym r) = Sym (bvtconcat l r)

instance
  (KnownNat n, KnownNat w, KnownNat w', n ~ (w' - w), w' ~ (w + n), 1 <= w, 1 <= n, 1 <= w') =>
  BVExtend (Sym (UnsignedBV w)) w' (Sym (UnsignedBV w'))
  where
  bvzeroExtend _ (Sym v) = Sym $ bvtext (Proxy @n) False v
  bvsignExtend _ (Sym v) = Sym $ bvtext (Proxy @n) True v
  bvextend = bvzeroExtend

instance
  ( KnownNat ix,
    KnownNat w,
    KnownNat ow,
    ix + w <= ow,
    1 <= ow,
    1 <= w
  ) =>
  BVSelect (Sym (UnsignedBV ow)) ix w (Sym (UnsignedBV w))
  where
  bvselect pix pw (Sym v) = Sym $ bvtselect pix pw v

instance (SupportedPrim (UnsignedBV n)) => Bits (Sym (UnsignedBV n)) where
  Sym l .&. Sym r = Sym $ withPrim @(UnsignedBV n) $ bitand l r
  Sym l .|. Sym r = Sym $ withPrim @(UnsignedBV n) $ bitor l r
  Sym l `xor` Sym r = Sym $ withPrim @(UnsignedBV n) $ bitxor l r
  complement (Sym n) = Sym $ withPrim @(UnsignedBV n) $ bitneg n
  shift (Sym n) i = Sym $ withPrim @(UnsignedBV n) $ bitshift n i
  rotate (Sym n) i = Sym $ withPrim @(UnsignedBV n) $ bitrotate n i
  bitSize _ = fromInteger $ withPrim @(UnsignedBV n) $ natVal (Proxy @n)
  bitSizeMaybe _ = Just $ fromInteger $ withPrim @(UnsignedBV n) $ natVal (Proxy @n)
  isSigned _ = False
  testBit (Conc n) = withPrim @(UnsignedBV n) $ testBit n
  testBit _ = error "You cannot call testBit on symbolic variables"
  bit = withPrim @(UnsignedBV n) $ conc . bit
  popCount (Conc n) = withPrim @(UnsignedBV n) $ popCount n
  popCount _ = error "You cannot call popCount on symbolic variables"

-- tabular func
type a =~> b = Sym (a =-> b)

infixr 0 =~>

instance (SupportedPrim a, SupportedPrim b) => Function (a =~> b) where
  type Arg (a =~> b) = Sym a
  type Ret (a =~> b) = Sym b
  (Sym f) # (Sym t) = Sym $ applyf f t

-- general func
type a -~> b = Sym (a --> b)

infixr 0 -~>

instance (SupportedPrim a, SupportedPrim b) => Function (a -~> b) where
  type Arg (a -~> b) = Sym a
  type Ret (a -~> b) = Sym b
  (Sym f) # (Sym t) = Sym $ applyg f t
