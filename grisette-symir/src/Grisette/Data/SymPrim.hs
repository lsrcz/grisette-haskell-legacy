{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DataKinds #-}
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
import Control.Monad.State
import Control.Monad.Reader
import Data.BitVector.Sized (knownNat, pattern BV)
import Data.BitVector.Sized.Signed (SignedBV (..), mkSignedBV)
import Data.BitVector.Sized.Unsigned
import Data.Bits
import Data.Char (chr, ord)
import Data.HashSet as S
import Data.Hashable
import Data.MemoTrie
import Data.Proxy
import Data.String
import GHC.Generics
import GHC.TypeLits
import Grisette.Control.Monad
import Grisette.Data.Class.BitVector
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Function
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.Evaluate
import Grisette.Data.Class.GenSym
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.MemoUtils
import Grisette.Data.Prim.BV
import Grisette.Data.Prim.Bits
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model
import Grisette.Data.Prim.Num
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.TabularFunc
import Language.Haskell.TH.Syntax
import Grisette.Data.GeneralFunc
import Grisette.Data.Prim.GeneralFunc

newtype Sym a = Sym {underlyingTerm :: Term a} deriving (Lift, Generic)

instance (SupportedPrim a) => HasTrie (Sym a) where
  newtype Sym a :->: b = SymTrie (Term a :->: b)
  trie f = SymTrie (trie (f . Sym))
  untrie (SymTrie t) = untrie t . underlyingTerm
  enumerate (SymTrie t) = enum' Sym t

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

-- bool
type SymBool = Sym Bool

instance SEq (Sym Bool) (Sym Bool) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance LogicalOp (Sym Bool) where
  (Sym l) ||~ (Sym r) = Sym $ orb l r
  (Sym l) &&~ (Sym r) = Sym $ andb l r
  nots (Sym v) = Sym $ notb v
  (Sym l) `xors` (Sym r) = Sym $ xorb l r
  (Sym l) `implies` (Sym r) = Sym $ implyb l r

instance SymBoolOp (Sym Bool)

{-
instance SymConcView Bool where
  symConcView (Sym (ConcTerm _ t)) = Just t
  symConcView _ = Nothing
  -}

-- integer
type SymInteger = Sym Integer

instance SEq (Sym Bool) (Sym Integer) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance Num (Sym Integer) where
  (Sym l) + (Sym r) = Sym $ addNum l r
  (Sym l) - (Sym r) = Sym $ minusNum l r
  (Sym l) * (Sym r) = Sym $ timesNum l r
  negate (Sym v) = Sym $ uminusNum v
  abs (Sym v) = Sym $ absNum v
  signum (Sym v) = Sym $ signumNum v
  fromInteger i = conc i

{-
instance SymConcView Integer where
  symConcView (Sym (IntegerConcTerm t)) = Just t
  symConcView _ = Nothing
  -}

instance SignedDivMod (Sym Bool) (Sym Integer) where
  divs (Sym l) rs@(Sym r) =
    withSimpleMergeableU @(Sym Bool) $
      mrgIf @(Sym Bool)
        (rs ==~ conc 0)
        (throwError $ transformError DivideByZero)
        (mrgReturn $ Sym $ divi l r)
  mods (Sym l) rs@(Sym r) =
    withSimpleMergeableU @(Sym Bool) $
      mrgIf @(Sym Bool)
        (rs ==~ conc 0)
        (throwError $ transformError DivideByZero)
        (mrgReturn $ Sym $ modi l r)

instance SOrd (Sym Bool) (Sym Integer) where
  (Sym a) <=~ (Sym b) = Sym $ leNum a b
  (Sym a) <~ (Sym b) = Sym $ ltNum a b
  (Sym a) >=~ (Sym b) = Sym $ geNum a b
  (Sym a) >~ (Sym b) = Sym $ gtNum a b
  a `symCompare` b =
    mrgIf
      (a <~ b)
      (mrgReturn LT)
      (mrgIf (a ==~ b) (mrgReturn EQ) (mrgReturn GT))

instance SymIntegerOp (Sym Bool) (Sym Integer)

-- signed bv
type SymSignedBV n = Sym (SignedBV n)

instance (SupportedPrim (SignedBV n)) => SEq (Sym Bool) (Sym (SignedBV n)) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

{-
instance (SupportedPrim (SignedBV n)) => SymConcView (SignedBV n) where
  symConcView (Sym x) = withPrim @(SignedBV n) $ case x of
    SignedBVConcTerm t -> Just t
    _ -> Nothing
    -}

instance (SupportedPrim (SignedBV n)) => Num (Sym (SignedBV n)) where
  (Sym l) + (Sym r) = Sym $ withPrim @(SignedBV n) $ addNum l r
  (Sym l) - (Sym r) = Sym $ withPrim @(SignedBV n) $ minusNum l r
  (Sym l) * (Sym r) = Sym $ withPrim @(SignedBV n) $ timesNum l r
  negate (Sym v) = Sym $ withPrim @(SignedBV n) $ uminusNum v
  abs (Sym v) = Sym $ withPrim @(SignedBV n) $ absNum v
  signum (Sym v) = Sym $ withPrim @(SignedBV n) $ signumNum v
  fromInteger i = withPrim @(SignedBV n) $ conc $ mkSignedBV knownNat i

instance (SupportedPrim (SignedBV n)) => SOrd (Sym Bool) (Sym (SignedBV n)) where
  (Sym a) <=~ (Sym b) = Sym $ withPrim @(SignedBV n) $ leNum a b
  (Sym a) <~ (Sym b) = Sym $ withPrim @(SignedBV n) $ ltNum a b
  (Sym a) >=~ (Sym b) = Sym $ withPrim @(SignedBV n) $ geNum a b
  (Sym a) >~ (Sym b) = Sym $ withPrim @(SignedBV n) $ gtNum a b

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

instance ToCon (SymSignedBV 8) Char where
  toCon (Conc (SignedBV (BV v))) = Just $ chr $ fromInteger v
  toCon _ = Nothing

instance ToSym Char (SymSignedBV 8) where
  toSym v = conc $ mkSignedBV (knownNat @8) $ toInteger $ ord v

-- unsigned bv
type SymUnsignedBV n = Sym (UnsignedBV n)

instance (SupportedPrim (UnsignedBV n)) => SEq (Sym Bool) (Sym (UnsignedBV n)) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

{-
instance (SupportedPrim (UnsignedBV n)) => SymConcView (UnsignedBV n) where
  symConcView (Sym x) = withPrim @(UnsignedBV n) $ case x of
    UnsignedBVConcTerm t -> Just t
    _ -> Nothing
    -}

instance (SupportedPrim (UnsignedBV n)) => Num (Sym (UnsignedBV n)) where
  (Sym l) + (Sym r) = Sym $ withPrim @(UnsignedBV n) $ addNum l r
  (Sym l) - (Sym r) = Sym $ withPrim @(UnsignedBV n) $ minusNum l r
  (Sym l) * (Sym r) = Sym $ withPrim @(UnsignedBV n) $ timesNum l r
  negate (Sym v) = Sym $ withPrim @(UnsignedBV n) $ uminusNum v
  abs (Sym v) = Sym $ withPrim @(UnsignedBV n) $ absNum v
  signum (Sym v) = Sym $ withPrim @(UnsignedBV n) $ signumNum v
  fromInteger i = withPrim @(UnsignedBV n) $ conc $ mkUnsignedBV knownNat i

instance (SupportedPrim (UnsignedBV n)) => SOrd (Sym Bool) (Sym (UnsignedBV n)) where
  (Sym a) <=~ (Sym b) = Sym $ withPrim @(UnsignedBV n) $ leNum a b
  (Sym a) <~ (Sym b) = Sym $ withPrim @(UnsignedBV n) $ ltNum a b
  (Sym a) >=~ (Sym b) = Sym $ withPrim @(UnsignedBV n) $ geNum a b
  (Sym a) >~ (Sym b) = Sym $ withPrim @(UnsignedBV n) $ gtNum a b

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

{-
instance (SupportedPrim a, SupportedPrim b) => SymConcView (a =-> b) where
  symConcView (Sym (TabularFuncConcTerm t)) = Just t
  symConcView _ = Nothing
  -}

{-
instance
  ( SupportedPrim a,
    SupportedPrim b,
    ExtractSymbolics (S.HashSet TermSymbol) a,
    ExtractSymbolics (S.HashSet TermSymbol) b
  ) =>
  ExtractSymbolics (S.HashSet TermSymbol) (a =~> b)
  where
  extractSymbolics (Sym t) = extractSymbolicsTerm t
-}