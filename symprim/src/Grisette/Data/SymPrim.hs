{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.SymPrim
  ( Sym (..),
    SymConcView (..),
    pattern SymConc,
    SymBool,
    SymInteger,
    type (=~>),
    SymSignedBV,
    SymUnsignedBV,
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.State
import Data.BitVector.Sized (knownNat)
import Data.BitVector.Sized.Signed (SignedBV, mkSignedBV)
import Data.BitVector.Sized.Unsigned
import Data.HashSet as S
import Data.Hashable
import GHC.Generics
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Function
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Prim.BV
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model
import Grisette.Data.Prim.Num
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.TabularFunc
import Language.Haskell.TH.Syntax
import Data.Bits
import Grisette.Data.Prim.Bits
import GHC.TypeLits
import Data.Proxy
import Data.String
import Data.MemoTrie
import Grisette.Data.MemoUtils

newtype Sym a = Sym {underlyingTerm :: Term a} deriving (Lift, Generic)

instance (SupportedPrim a) => HasTrie (Sym a) where
  newtype Sym a :->: b = SymTrie (Term a :->: b)
  trie f = SymTrie (trie (f . Sym))
  untrie (SymTrie t) = untrie t . underlyingTerm
  enumerate (SymTrie t) = enum' Sym t

instance NFData (Sym a) where
  rnf (Sym t) = rnf t

class SupportedPrim a => SymConcView a where
  symConcView :: Sym a -> Maybe a

pattern SymConc :: SymConcView a => a -> Sym a
pattern SymConc c <-
  (Sym (ConcTerm _ c))
  where
    SymConc c = conc c

instance (SupportedPrim a) => ITEOp (Sym Bool) (Sym a) where
  ites (Sym c) (Sym t) (Sym f) = Sym $ iteterm c t f

instance (SupportedPrim a) => Mergeable (Sym Bool) (Sym a) where
  mergeStrategy = SimpleStrategy ites

instance (SupportedPrim a) => SimpleMergeable (Sym Bool) (Sym a) where
  mrgIf = ites

instance (SymConcView a) => PrimWrapper (Sym a) a where
  conc = Sym . concTerm
  ssymb = Sym . ssymbTerm
  isymb i str = Sym $ isymbTerm i str
  concView (SymConc t) = Just t
  concView _ = Nothing

instance (SymConcView t) => IsString (Sym t) where
  fromString = ssymb

instance (SupportedPrim a) => ToSym (Sym a) (Sym a) where
  toSym = id

instance (SymConcView a) => ToSym a (Sym a) where
  toSym = conc

instance (SupportedPrim a) => ToCon (Sym a) (Sym a) where
  toCon = Just

instance (SymConcView a) => ToCon (Sym a) a where
  toCon = symConcView

instance (SupportedPrim a) => SymEval Model (Sym a) where
  symeval fillDefault model (Sym t) = Sym $ evaluateTerm fillDefault model t

instance (SupportedPrim a) => ExtractSymbolics (S.HashSet TermSymbol) (Sym a) where
  extractSymbolics (Sym t) = extractSymbolicsTerm t

instance (SymBoolOp (Sym Bool), SupportedPrim a, SymConcView a) => SymGen (Sym Bool) () (Sym a) where
  genSymIndexed _ = mrgSingle <$> genSymSimpleIndexed @(Sym Bool) ()

instance (SymBoolOp (Sym Bool), SupportedPrim a, SymConcView a) => SymGenSimple (Sym Bool) () (Sym a) where
  genSymSimpleIndexed _ = do
    (i, s) <- get
    put (i + 1, s)
    return $ isymb i s

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

instance SymBoolOp (Sym Bool)

instance SymConcView Bool where
  symConcView (Sym (BoolConcTerm t)) = Just t
  symConcView _ = Nothing

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

instance SymConcView Integer where
  symConcView (Sym (IntegerConcTerm t)) = Just t
  symConcView _ = Nothing

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

instance SymIntegerOp (Sym Bool) (Sym Integer)

-- signed bv
type SymSignedBV n = Sym (SignedBV n)

instance (SupportedPrim (SignedBV n)) => SEq (Sym Bool) (Sym (SignedBV n)) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance (SupportedPrim (SignedBV n)) => SymConcView (SignedBV n) where
  symConcView (Sym x) = withPrim @(SignedBV n) $ case x of
    SignedBVConcTerm t -> Just t
    _ -> Nothing

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
  popCount _ = error "You cannot call popCount on symbolic variables"

-- unsigned bv
type SymUnsignedBV n = Sym (UnsignedBV n)

instance (SupportedPrim (UnsignedBV n)) => SEq (Sym Bool) (Sym (UnsignedBV n)) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance (SupportedPrim (UnsignedBV n)) => SymConcView (UnsignedBV n) where
  symConcView (Sym x) = withPrim @(UnsignedBV n) $ case x of
    UnsignedBVConcTerm t -> Just t
    _ -> Nothing

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

-- tabular func
type a =~> b = Sym (a =-> b)

instance (SupportedPrim a, SupportedPrim b) => Function (a =~> b) where
  type Arg (a =~> b) = Sym a
  type Ret (a =~> b) = Sym b
  (Sym f) # t = Sym $ applyf f (underlyingTerm t)

instance (SupportedPrim a, SupportedPrim b) => SymConcView (a =-> b) where
  symConcView (Sym (TabularFuncConcTerm t)) = Just t
  symConcView _ = Nothing

instance
  ( SupportedPrim a,
    SupportedPrim b,
    ExtractSymbolics (S.HashSet TermSymbol) a,
    ExtractSymbolics (S.HashSet TermSymbol) b
  ) =>
  ExtractSymbolics (S.HashSet TermSymbol) (a =~> b)
  where
  extractSymbolics (Sym t) = extractSymbolicsTerm t

instance (SupportedPrim (UnsignedBV n)) => Bits (Sym (UnsignedBV n)) where
  Sym l .&. Sym r = Sym $ withPrim @(UnsignedBV n) $ bitand l r
  Sym l .|. Sym r = Sym $ withPrim @(UnsignedBV n) $ bitor l r
  Sym l `xor` Sym r = Sym $ withPrim @(UnsignedBV n) $ bitxor l r
  complement (Sym n) = Sym $ withPrim @(UnsignedBV n) $ bitneg n
  shift (Sym n) i = Sym $ withPrim @(UnsignedBV n) $ bitshift n i
  rotate (Sym n) i = Sym $ withPrim @(UnsignedBV n) $ bitrotate n i
  bitSize _ = fromInteger $ withPrim @(UnsignedBV n) $ natVal (Proxy @n)
  bitSizeMaybe _ = Just $ fromInteger $ withPrim @(UnsignedBV n) $ natVal (Proxy @n)
  isSigned _ = True
  testBit (Conc n) = withPrim @(UnsignedBV n) $ testBit n
  testBit _ = error "You cannot call testBit on symbolic variables"
  bit = withPrim @(UnsignedBV n) $ conc . bit
  popCount _ = error "You cannot call popCount on symbolic variables"
