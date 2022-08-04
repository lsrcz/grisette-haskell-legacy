{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.IR.SymPrim.Data.SymPrim
  ( Sym (..),
    --SymConcView (..),
    --pattern SymConc,
    SymBool,
    SymInteger,
    type (=~>),
    type (-~>),
    SymWordN,
    SymIntN,
    symSize,
    symsSize,
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Data.Bits
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
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.GeneralFunc
import Grisette.IR.SymPrim.Data.IntBitwidth
import Grisette.IR.SymPrim.Data.Prim.BV
import Grisette.IR.SymPrim.Data.Prim.Bits
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.GeneralFunc
import Grisette.IR.SymPrim.Data.Prim.Integer
import Grisette.IR.SymPrim.Data.Prim.InternedTerm
import Grisette.IR.SymPrim.Data.Prim.Model
import Grisette.IR.SymPrim.Data.Prim.Num
import Grisette.IR.SymPrim.Data.Prim.TabularFunc
import Grisette.IR.SymPrim.Data.TabularFunc
import Grisette.Lib.Control.Monad
import Language.Haskell.TH.Syntax

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
  mergingStrategy = SimpleStrategy ites

instance (SupportedPrim a) => SimpleMergeable (Sym Bool) (Sym a) where
  mrgIte = ites

instance (SupportedPrim a) => PrimWrapper (Sym a) a where
  conc = Sym . concTerm
  ssymb = Sym . ssymbTerm
  isymb str i = Sym $ isymbTerm str i
  sinfosymb str info = Sym $ sinfosymbTerm str info
  iinfosymb str i info = Sym $ iinfosymbTerm str i info
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
  genSymFresh _ = mrgReturn <$> genSymSimpleFresh ()

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSymSimple () (Sym a) where
  genSymSimpleFresh _ = do
    ident <- getGenSymIdent
    GenSymIndex i <- nextGenSymIndex
    case ident of
      GenSymIdent s -> return $ isymb s i
      GenSymIdentWithInfo s info -> return $ iinfosymb s i info

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSym (Sym Bool) (Sym a) (Sym a)

instance (SymBoolOp (Sym Bool), SupportedPrim a) => GenSymSimple (Sym a) (Sym a) where
  genSymSimpleFresh _ = genSymSimpleFresh ()

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
SEQ_SYM (IntN n)
SEQ_SYM (WordN n)
SORD_SYM (Integer)
SORD_SYM (IntN n)
SORD_SYM (WordN n)

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
type SymIntN n = Sym (IntN n)

instance (SupportedPrim (IntN n)) => Num (Sym (IntN n)) where
  (Sym l) + (Sym r) = Sym $ withPrim @(IntN n) $ addNum l r
  (Sym l) - (Sym r) = Sym $ withPrim @(IntN n) $ minusNum l r
  (Sym l) * (Sym r) = Sym $ withPrim @(IntN n) $ timesNum l r
  negate (Sym v) = Sym $ withPrim @(IntN n) $ uminusNum v
  abs (Sym v) = Sym $ withPrim @(IntN n) $ absNum v
  signum (Sym v) = Sym $ withPrim @(IntN n) $ signumNum v
  fromInteger i = withPrim @(IntN n) $ conc $ fromInteger i

instance (SupportedPrim (IntN n)) => Bits (Sym (IntN n)) where
  Sym l .&. Sym r = Sym $ withPrim @(IntN n) $ bitand l r
  Sym l .|. Sym r = Sym $ withPrim @(IntN n) $ bitor l r
  Sym l `xor` Sym r = Sym $ withPrim @(IntN n) $ bitxor l r
  complement (Sym n) = Sym $ withPrim @(IntN n) $ bitneg n
  shift (Sym n) i = Sym $ withPrim @(IntN n) $ bitshift n i
  rotate (Sym n) i = Sym $ withPrim @(IntN n) $ bitrotate n i
  bitSize _ = fromInteger $ withPrim @(IntN n) $ natVal (Proxy @n)
  bitSizeMaybe _ = Just $ fromInteger $ withPrim @(IntN n) $ natVal (Proxy @n)
  isSigned _ = True
  testBit (Conc n) = withPrim @(IntN n) $ testBit n
  testBit _ = error "You cannot call testBit on symbolic variables"
  bit = withPrim @(IntN n) $ conc . bit
  popCount (Conc n) = withPrim @(IntN n) $ popCount n
  popCount _ = error "You cannot call popCount on symbolic variables"

instance
  (KnownNat w', KnownNat n, KnownNat w, w' ~ (n + w), 1 <= n, 1 <= w, 1 <= w') =>
  BVConcat (Sym (IntN n)) (Sym (IntN w)) (Sym (IntN w'))
  where
  bvconcat (Sym l) (Sym r) = Sym (bvtconcat l r)

instance
  ( KnownNat w,
    KnownNat w',
    1 <= w,
    1 <= w',
    w <= w',
    w + 1 <= w',
    1 <= w' - w,
    KnownNat (w' - w)
  ) =>
  BVExtend (Sym (IntN w)) w' (Sym (IntN w'))
  where
  bvzeroExtend _ (Sym v) = Sym $ bvtext (Proxy @w') False v
  bvsignExtend _ (Sym v) = Sym $ bvtext (Proxy @w') True v
  bvextend = bvsignExtend

instance
  ( KnownNat ix,
    KnownNat w,
    KnownNat ow,
    ix + w <= ow,
    1 <= ow,
    1 <= w
  ) =>
  BVSelect (Sym (IntN ow)) ix w (Sym (IntN w))
  where
  bvselect pix pw (Sym v) = Sym $ bvtselect pix pw v

#define TOSYM_MACHINE_INTEGER(int, bv) \
instance ToSym (int) (Sym (bv)) where \
  toSym = fromIntegral

#define TOCON_MACHINE_INTEGER(bvw, n, int) \
instance ToCon (Sym (bvw n)) (int) where \
  toCon (Conc (bvw v :: bvw n)) = Just $ fromIntegral v; \
  toCon _ = Nothing

TOSYM_MACHINE_INTEGER (Int8, IntN 8)
TOSYM_MACHINE_INTEGER (Int16, IntN 16)
TOSYM_MACHINE_INTEGER (Int32, IntN 32)
TOSYM_MACHINE_INTEGER (Int64, IntN 64)
TOSYM_MACHINE_INTEGER (Word8, WordN 8)
TOSYM_MACHINE_INTEGER (Word16, WordN 16)
TOSYM_MACHINE_INTEGER (Word32, WordN 32)
TOSYM_MACHINE_INTEGER (Word64, WordN 64)
TOSYM_MACHINE_INTEGER (Int, IntN $(intBitwidthQ))
TOSYM_MACHINE_INTEGER (Word, WordN $(intBitwidthQ))

TOCON_MACHINE_INTEGER (IntN, 8, Int8)
TOCON_MACHINE_INTEGER (IntN, 16, Int16)
TOCON_MACHINE_INTEGER (IntN, 32, Int32)
TOCON_MACHINE_INTEGER (IntN, 64, Int64)
TOCON_MACHINE_INTEGER (WordN, 8, Word8)
TOCON_MACHINE_INTEGER (WordN, 16, Word16)
TOCON_MACHINE_INTEGER (WordN, 32, Word32)
TOCON_MACHINE_INTEGER (WordN, 64, Word64)
TOCON_MACHINE_INTEGER (IntN, $(intBitwidthQ), Int)
TOCON_MACHINE_INTEGER (WordN, $(intBitwidthQ), Word)

-- unsigned bv
type SymWordN n = Sym (WordN n)

instance (SupportedPrim (WordN n)) => Num (Sym (WordN n)) where
  (Sym l) + (Sym r) = Sym $ withPrim @(WordN n) $ addNum l r
  (Sym l) - (Sym r) = Sym $ withPrim @(WordN n) $ minusNum l r
  (Sym l) * (Sym r) = Sym $ withPrim @(WordN n) $ timesNum l r
  negate (Sym v) = Sym $ withPrim @(WordN n) $ uminusNum v
  abs (Sym v) = Sym $ withPrim @(WordN n) $ absNum v
  signum (Sym v) = Sym $ withPrim @(WordN n) $ signumNum v
  fromInteger i = withPrim @(WordN n) $ conc $ fromInteger i

instance
  (KnownNat w', KnownNat n, KnownNat w, w' ~ (n + w), 1 <= n, 1 <= w, 1 <= w') =>
  BVConcat (Sym (WordN n)) (Sym (WordN w)) (Sym (WordN w'))
  where
  bvconcat (Sym l) (Sym r) = Sym (bvtconcat l r)

instance
  ( KnownNat w,
    KnownNat w',
    1 <= w,
    1 <= w',
    w + 1 <= w',
    w <= w',
    1 <= w' - w,
    KnownNat (w' - w)
  ) =>
  BVExtend (Sym (WordN w)) w' (Sym (WordN w'))
  where
  bvzeroExtend _ (Sym v) = Sym $ bvtext (Proxy @w') False v
  bvsignExtend _ (Sym v) = Sym $ bvtext (Proxy @w') True v
  bvextend = bvzeroExtend

instance
  ( KnownNat ix,
    KnownNat w,
    KnownNat ow,
    ix + w <= ow,
    1 <= ow,
    1 <= w
  ) =>
  BVSelect (Sym (WordN ow)) ix w (Sym (WordN w))
  where
  bvselect pix pw (Sym v) = Sym $ bvtselect pix pw v

instance (SupportedPrim (WordN n)) => Bits (Sym (WordN n)) where
  Sym l .&. Sym r = Sym $ withPrim @(WordN n) $ bitand l r
  Sym l .|. Sym r = Sym $ withPrim @(WordN n) $ bitor l r
  Sym l `xor` Sym r = Sym $ withPrim @(WordN n) $ bitxor l r
  complement (Sym n) = Sym $ withPrim @(WordN n) $ bitneg n
  shift (Sym n) i = Sym $ withPrim @(WordN n) $ bitshift n i
  rotate (Sym n) i = Sym $ withPrim @(WordN n) $ bitrotate n i
  bitSize _ = fromInteger $ withPrim @(WordN n) $ natVal (Proxy @n)
  bitSizeMaybe _ = Just $ fromInteger $ withPrim @(WordN n) $ natVal (Proxy @n)
  isSigned _ = False
  testBit (Conc n) = withPrim @(WordN n) $ testBit n
  testBit _ = error "You cannot call testBit on symbolic variables"
  bit = withPrim @(WordN n) $ conc . bit
  popCount (Conc n) = withPrim @(WordN n) $ popCount n
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

symsSize :: [Sym a] -> Int
symsSize = termsSize . fmap underlyingTerm

symSize :: Sym a -> Int
symSize = termSize . underlyingTerm
