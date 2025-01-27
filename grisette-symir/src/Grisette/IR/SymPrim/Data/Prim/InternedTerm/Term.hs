{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
  ( SupportedPrim (..),
    UnaryOp (..),
    BinaryOp (..),
    TernaryOp (..),
    Symbol (..),
    TermSymbol (..),
    termSymbol,
    Term (..),
    UTerm (..),
    FuncArg (..),
    type (-->) (..),
  )
where

import Control.DeepSeq
import Data.Bits
import Data.Function (on)
import Data.Hashable
import Data.Interned
import Data.Kind
import Data.Typeable (Proxy (..), cast)
import GHC.Generics
import GHC.TypeNats
import Grisette.Core.Data.Class.BitVector
import Grisette.Core.Data.Class.Function
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Caches
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.Prim.InternedTerm.GeneralFuncSubst
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.Prim.ModelValue
import Grisette.IR.SymPrim.Data.Prim.Utils
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.TabularFunc
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax.Compat
import Type.Reflection

class (Lift t, Typeable t, Hashable t, Eq t, Show t, NFData t) => SupportedPrim t where
  type PrimConstraint t :: Constraint
  type PrimConstraint t = ()
  default withPrim :: PrimConstraint t => proxy t -> (PrimConstraint t => a) -> a
  withPrim :: proxy t -> (PrimConstraint t => a) -> a
  withPrim _ i = i
  termCache :: Cache (Term t)
  termCache = typeMemoizedCache
  pformatConc :: t -> String
  default pformatConc :: (Show t) => t -> String
  pformatConc = show
  pformatSymb :: proxy t -> Symbol -> String
  pformatSymb _ = show
  defaultValue :: t
  defaultValueDynamic :: proxy t -> ModelValue
  defaultValueDynamic _ = toModelValue (defaultValue @t)

class
  (SupportedPrim arg, SupportedPrim t, Lift tag, NFData tag, Show tag, Typeable tag, Eq tag, Hashable tag) =>
  UnaryOp tag arg t
    | tag arg -> t
  where
  partialEvalUnary :: (Typeable tag, Typeable t) => tag -> Term arg -> Term t
  pformatUnary :: tag -> Term arg -> String

class
  ( SupportedPrim arg1,
    SupportedPrim arg2,
    SupportedPrim t,
    Lift tag,
    NFData tag,
    Show tag,
    Typeable tag,
    Eq tag,
    Hashable tag
  ) =>
  BinaryOp tag arg1 arg2 t
    | tag arg1 arg2 -> t
  where
  partialEvalBinary :: (Typeable tag, Typeable t) => tag -> Term arg1 -> Term arg2 -> Term t
  pformatBinary :: tag -> Term arg1 -> Term arg2 -> String

class
  ( SupportedPrim arg1,
    SupportedPrim arg2,
    SupportedPrim arg3,
    SupportedPrim t,
    Lift tag,
    NFData tag,
    Show tag,
    Typeable tag,
    Eq tag,
    Hashable tag
  ) =>
  TernaryOp tag arg1 arg2 arg3 t
    | tag arg1 arg2 arg3 -> t
  where
  partialEvalTernary :: (Typeable tag, Typeable t) => tag -> Term arg1 -> Term arg2 -> Term arg3 -> Term t
  pformatTernary :: tag -> Term arg1 -> Term arg2 -> Term arg3 -> String

data Symbol where
  SimpleSymbol :: String -> Symbol
  IndexedSymbol :: String -> Int -> Symbol
  WithInfo :: forall a. (Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => Symbol -> a -> Symbol

-- deriving (Eq, Ord, Generic, Lift, NFData)

instance Eq Symbol where
  SimpleSymbol x == SimpleSymbol y = x == y
  IndexedSymbol x i == IndexedSymbol y j = i == j && x == y
  WithInfo s1 (i1 :: a) == WithInfo s2 (i2 :: b) = case eqTypeRep (typeRep @a) (typeRep @b) of
    Just HRefl -> i1 == i2 && s1 == s2
    _ -> False
  _ == _ = False

instance Ord Symbol where
  SimpleSymbol x <= SimpleSymbol y = x <= y
  IndexedSymbol x i <= IndexedSymbol y j = i < j || (i == j && x <= y)
  WithInfo s1 (i1 :: a) <= WithInfo s2 (i2 :: b) = case eqTypeRep (typeRep @a) (typeRep @b) of
    Just HRefl -> s1 < s2 || (s1 == s2 && i1 <= i2)
    _ -> False
  _ <= _ = False

instance Lift Symbol where
  liftTyped (SimpleSymbol x) = [||SimpleSymbol x||]
  liftTyped (IndexedSymbol x i) = [||IndexedSymbol x i||]
  liftTyped (WithInfo s1 i1) = [||WithInfo s1 i1||]

instance Show Symbol where
  show (SimpleSymbol str) = str
  show (IndexedSymbol str i) = str ++ "@" ++ show i
  show (WithInfo s info) = show s ++ ":" ++ show info

instance Hashable Symbol where
  s `hashWithSalt` SimpleSymbol x = s `hashWithSalt` x
  s `hashWithSalt` IndexedSymbol x i = s `hashWithSalt` x `hashWithSalt` i
  s `hashWithSalt` WithInfo sym info = s `hashWithSalt` sym `hashWithSalt` info

instance NFData Symbol where
  rnf (SimpleSymbol str) = rnf str
  rnf (IndexedSymbol str i) = rnf str `seq` rnf i
  rnf (WithInfo s info) = rnf s `seq` rnf info

data TermSymbol where
  TermSymbol :: forall t. (SupportedPrim t) => TypeRep t -> Symbol -> TermSymbol

termSymbol :: forall proxy t. (SupportedPrim t) => proxy t -> Symbol -> TermSymbol
termSymbol _ = TermSymbol (typeRep @t)

instance NFData TermSymbol where
  rnf (TermSymbol p s) = rnf (SomeTypeRep p) `seq` rnf s

instance Eq TermSymbol where
  (TermSymbol t1 s1) == (TermSymbol t2 s2) = s1 == s2 && eqTypeRepBool t1 t2

instance Ord TermSymbol where
  (TermSymbol t1 s1) <= (TermSymbol t2 s2) = SomeTypeRep t1 < SomeTypeRep t2 || (eqTypeRepBool t1 t2 && s1 <= s2)

instance Hashable TermSymbol where
  hashWithSalt s (TermSymbol t1 s1) = s `hashWithSalt` s1 `hashWithSalt` t1

instance Show TermSymbol where
  show (TermSymbol t s) = show s ++ " :: " ++ show t

data Term t where
  ConcTerm :: (SupportedPrim t) => {-# UNPACK #-} !Id -> !t -> Term t
  SymbTerm :: (SupportedPrim t) => {-# UNPACK #-} !Id -> !TermSymbol -> Term t
  UnaryTerm ::
    (UnaryOp tag arg t) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg) ->
    Term t
  BinaryTerm ::
    (BinaryOp tag arg1 arg2 t) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    Term t
  TernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    !(Term arg3) ->
    Term t
  NotTerm :: {-# UNPACK #-} !Id -> !(Term Bool) -> Term Bool
  OrTerm :: {-# UNPACK #-} !Id -> !(Term Bool) -> !(Term Bool) -> Term Bool
  AndTerm :: {-# UNPACK #-} !Id -> !(Term Bool) -> !(Term Bool) -> Term Bool
  EqvTerm :: SupportedPrim t => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term Bool
  ITETerm :: SupportedPrim t => {-# UNPACK #-} !Id -> !(Term Bool) -> !(Term t) -> !(Term t) -> Term t
  AddNumTerm :: (SupportedPrim t, Num t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term t
  UMinusNumTerm :: (SupportedPrim t, Num t) => {-# UNPACK #-} !Id -> !(Term t) -> Term t
  TimesNumTerm :: (SupportedPrim t, Num t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term t
  AbsNumTerm :: (SupportedPrim t, Num t) => {-# UNPACK #-} !Id -> !(Term t) -> Term t
  SignumNumTerm :: (SupportedPrim t, Num t) => {-# UNPACK #-} !Id -> !(Term t) -> Term t
  LTNumTerm :: (SupportedPrim t, Num t, Ord t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term Bool
  LENumTerm :: (SupportedPrim t, Num t, Ord t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term Bool
  AndBitsTerm :: (SupportedPrim t, Bits t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term t
  OrBitsTerm :: (SupportedPrim t, Bits t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term t
  XorBitsTerm :: (SupportedPrim t, Bits t) => {-# UNPACK #-} !Id -> !(Term t) -> !(Term t) -> Term t
  ComplementBitsTerm :: (SupportedPrim t, Bits t) => {-# UNPACK #-} !Id -> !(Term t) -> Term t
  ShiftBitsTerm :: (SupportedPrim t, Bits t) => {-# UNPACK #-} !Id -> !(Term t) -> {-# UNPACK #-} !Int -> Term t
  RotateBitsTerm :: (SupportedPrim t, Bits t) => {-# UNPACK #-} !Id -> !(Term t) -> {-# UNPACK #-} !Int -> Term t
  BVConcatTerm ::
    ( SupportedPrim (bv a),
      SupportedPrim (bv b),
      SupportedPrim (bv c),
      KnownNat a,
      KnownNat b,
      KnownNat c,
      BVConcat (bv a) (bv b) (bv c)
    ) =>
    {-# UNPACK #-} !Id ->
    !(Term (bv a)) ->
    !(Term (bv b)) ->
    Term (bv c)
  BVSelectTerm ::
    ( SupportedPrim (bv a),
      SupportedPrim (bv w),
      KnownNat a,
      KnownNat w,
      KnownNat ix,
      BVSelect (bv a) ix w (bv w)
    ) =>
    {-# UNPACK #-} !Id ->
    !(TypeRep ix) ->
    !(TypeRep w) ->
    !(Term (bv a)) ->
    Term (bv w)
  BVExtendTerm ::
    ( SupportedPrim (bv a),
      SupportedPrim (bv b),
      KnownNat a,
      KnownNat b,
      KnownNat n,
      BVExtend (bv a) n (bv b)
    ) =>
    {-# UNPACK #-} !Id ->
    !Bool ->
    !(TypeRep n) ->
    !(Term (bv a)) ->
    Term (bv b)
  TabularFuncApplyTerm ::
    ( SupportedPrim a,
      SupportedPrim b
    ) =>
    {-# UNPACK #-} !Id ->
    Term (a =-> b) ->
    Term a ->
    Term b
  GeneralFuncApplyTerm ::
    ( SupportedPrim a,
      SupportedPrim b
    ) =>
    {-# UNPACK #-} !Id ->
    Term (a --> b) ->
    Term a ->
    Term b
  DivIntegerTerm :: !Id -> Term Integer -> Term Integer -> Term Integer
  ModIntegerTerm :: !Id -> Term Integer -> Term Integer -> Term Integer

instance NFData (Term a) where
  rnf i = identity i `seq` ()

instance Lift (Term t) where
  lift = unTypeSplice . liftTyped
  liftTyped (ConcTerm _ i) = [||concTerm i||]
  liftTyped (SymbTerm _ (TermSymbol _ sym)) = [||symbTerm sym||]
  liftTyped (UnaryTerm _ tag arg) = [||constructUnary tag arg||]
  liftTyped (BinaryTerm _ tag arg1 arg2) = [||constructBinary tag arg1 arg2||]
  liftTyped (TernaryTerm _ tag arg1 arg2 arg3) = [||constructTernary tag arg1 arg2 arg3||]
  liftTyped (NotTerm _ arg) = [||notTerm arg||]
  liftTyped (OrTerm _ arg1 arg2) = [||orTerm arg1 arg2||]
  liftTyped (AndTerm _ arg1 arg2) = [||andTerm arg1 arg2||]
  liftTyped (EqvTerm _ arg1 arg2) = [||eqvTerm arg1 arg2||]
  liftTyped (ITETerm _ cond arg1 arg2) = [||iteTerm cond arg1 arg2||]
  liftTyped (AddNumTerm _ arg1 arg2) = [||addNumTerm arg1 arg2||]
  liftTyped (UMinusNumTerm _ arg) = [||uminusNumTerm arg||]
  liftTyped (TimesNumTerm _ arg1 arg2) = [||timesNumTerm arg1 arg2||]
  liftTyped (AbsNumTerm _ arg) = [||absNumTerm arg||]
  liftTyped (SignumNumTerm _ arg) = [||signumNumTerm arg||]
  liftTyped (LTNumTerm _ arg1 arg2) = [||ltNumTerm arg1 arg2||]
  liftTyped (LENumTerm _ arg1 arg2) = [||leNumTerm arg1 arg2||]
  liftTyped (AndBitsTerm _ arg1 arg2) = [||andBitsTerm arg1 arg2||]
  liftTyped (OrBitsTerm _ arg1 arg2) = [||orBitsTerm arg1 arg2||]
  liftTyped (XorBitsTerm _ arg1 arg2) = [||xorBitsTerm arg1 arg2||]
  liftTyped (ComplementBitsTerm _ arg) = [||complementBitsTerm arg||]
  liftTyped (ShiftBitsTerm _ arg n) = [||shiftBitsTerm arg n||]
  liftTyped (RotateBitsTerm _ arg n) = [||rotateBitsTerm arg n||]
  liftTyped (BVConcatTerm _ arg1 arg2) = [||bvconcatTerm arg1 arg2||]
  liftTyped (BVSelectTerm _ (_ :: TypeRep ix) (_ :: TypeRep w) arg) = [||bvselectTerm (Proxy @ix) (Proxy @w) arg||]
  liftTyped (BVExtendTerm _ signed (_ :: TypeRep n) arg) = [||bvextendTerm signed (Proxy @n) arg||]
  liftTyped (TabularFuncApplyTerm _ func arg) = [||tabularFuncApplyTerm func arg||]
  liftTyped (GeneralFuncApplyTerm _ func arg) = [||generalFuncApplyTerm func arg||]
  liftTyped (DivIntegerTerm _ arg1 arg2) = [||divIntegerTerm arg1 arg2||]
  liftTyped (ModIntegerTerm _ arg1 arg2) = [||modIntegerTerm arg1 arg2||]

instance Show (Term ty) where
  show (ConcTerm i v) = "ConcTerm{id=" ++ show i ++ ", v=" ++ show v ++ "}"
  show (SymbTerm i name) =
    "SymbTerm{id="
      ++ show i
      ++ ", name="
      ++ show name
      ++ ", type="
      ++ show (typeRep @ty)
      ++ "}"
  show (UnaryTerm i tag arg) = "Unary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg=" ++ show arg ++ "}"
  show (BinaryTerm i tag arg1 arg2) =
    "Binary{id="
      ++ show i
      ++ ", tag="
      ++ show tag
      ++ ", arg1="
      ++ show arg1
      ++ ", arg2="
      ++ show arg2
      ++ "}"
  show (TernaryTerm i tag arg1 arg2 arg3) =
    "Ternary{id="
      ++ show i
      ++ ", tag="
      ++ show tag
      ++ ", arg1="
      ++ show arg1
      ++ ", arg2="
      ++ show arg2
      ++ ", arg3="
      ++ show arg3
      ++ "}"
  show (NotTerm i arg) = "Not{id=" ++ show i ++ ", arg=" ++ show arg ++ "}"
  show (OrTerm i arg1 arg2) = "Or{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (AndTerm i arg1 arg2) = "And{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (EqvTerm i arg1 arg2) = "Eqv{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (ITETerm i cond l r) =
    "ITE{id="
      ++ show i
      ++ ", cond="
      ++ show cond
      ++ ", then="
      ++ show l
      ++ ", else="
      ++ show r
      ++ "}"
  show (AddNumTerm i arg1 arg2) = "AddNum{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (UMinusNumTerm i arg) = "UMinusNum{id=" ++ show i ++ ", arg=" ++ show arg ++ "}"
  show (TimesNumTerm i arg1 arg2) = "TimesNum{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (AbsNumTerm i arg) = "AbsNum{id=" ++ show i ++ ", arg=" ++ show arg ++ "}"
  show (SignumNumTerm i arg) = "SignumNum{id=" ++ show i ++ ", arg=" ++ show arg ++ "}"
  show (LTNumTerm i arg1 arg2) = "LTNum{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (LENumTerm i arg1 arg2) = "LENum{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (AndBitsTerm i arg1 arg2) = "AndBits{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (OrBitsTerm i arg1 arg2) = "OrBits{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (XorBitsTerm i arg1 arg2) = "XorBits{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (ComplementBitsTerm i arg) = "ComplementBits{id=" ++ show i ++ ", arg=" ++ show arg ++ "}"
  show (ShiftBitsTerm i arg n) = "ShiftBits{id=" ++ show i ++ ", arg=" ++ show arg ++ ", n=" ++ show n ++ "}"
  show (RotateBitsTerm i arg n) = "RotateBits{id=" ++ show i ++ ", arg=" ++ show arg ++ ", n=" ++ show n ++ "}"
  show (BVConcatTerm i arg1 arg2) = "BVConcat{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (BVSelectTerm i ix w arg) =
    "BVSelect{id=" ++ show i ++ ", ix=" ++ show ix ++ ", w=" ++ show w ++ ", arg=" ++ show arg ++ "}"
  show (BVExtendTerm i signed n arg) =
    "BVExtend{id=" ++ show i ++ ", signed=" ++ show signed ++ ", n=" ++ show n ++ ", arg=" ++ show arg ++ "}"
  show (TabularFuncApplyTerm i func arg) =
    "TabularFuncApply{id=" ++ show i ++ ", func=" ++ show func ++ ", arg=" ++ show arg ++ "}"
  show (GeneralFuncApplyTerm i func arg) =
    "GeneralFuncApply{id=" ++ show i ++ ", func=" ++ show func ++ ", arg=" ++ show arg ++ "}"
  show (DivIntegerTerm i arg1 arg2) =
    "DivInteger{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"
  show (ModIntegerTerm i arg1 arg2) =
    "ModInteger{id=" ++ show i ++ ", arg1=" ++ show arg1 ++ ", arg2=" ++ show arg2 ++ "}"

instance (SupportedPrim t) => Eq (Term t) where
  (==) = (==) `on` identity

instance (SupportedPrim t) => Hashable (Term t) where
  hashWithSalt s t = hashWithSalt s $ identity t

data UTerm t where
  UConcTerm :: (SupportedPrim t) => !t -> UTerm t
  USymbTerm :: (SupportedPrim t) => !TermSymbol -> UTerm t
  UUnaryTerm :: (UnaryOp tag arg t) => !tag -> !(Term arg) -> UTerm t
  UBinaryTerm ::
    (BinaryOp tag arg1 arg2 t) =>
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    UTerm t
  UTernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t) =>
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    !(Term arg3) ->
    UTerm t
  UNotTerm :: !(Term Bool) -> UTerm Bool
  UOrTerm :: !(Term Bool) -> !(Term Bool) -> UTerm Bool
  UAndTerm :: !(Term Bool) -> !(Term Bool) -> UTerm Bool
  UEqvTerm :: SupportedPrim t => !(Term t) -> !(Term t) -> UTerm Bool
  UITETerm :: SupportedPrim t => !(Term Bool) -> !(Term t) -> !(Term t) -> UTerm t
  UAddNumTerm :: (SupportedPrim t, Num t) => !(Term t) -> !(Term t) -> UTerm t
  UUMinusNumTerm :: (SupportedPrim t, Num t) => !(Term t) -> UTerm t
  UTimesNumTerm :: (SupportedPrim t, Num t) => !(Term t) -> !(Term t) -> UTerm t
  UAbsNumTerm :: (SupportedPrim t, Num t) => !(Term t) -> UTerm t
  USignumNumTerm :: (SupportedPrim t, Num t) => !(Term t) -> UTerm t
  ULTNumTerm :: (SupportedPrim t, Num t, Ord t) => !(Term t) -> !(Term t) -> UTerm Bool
  ULENumTerm :: (SupportedPrim t, Num t, Ord t) => !(Term t) -> !(Term t) -> UTerm Bool
  UAndBitsTerm :: (SupportedPrim t, Bits t) => !(Term t) -> !(Term t) -> UTerm t
  UOrBitsTerm :: (SupportedPrim t, Bits t) => !(Term t) -> !(Term t) -> UTerm t
  UXorBitsTerm :: (SupportedPrim t, Bits t) => !(Term t) -> !(Term t) -> UTerm t
  UComplementBitsTerm :: (SupportedPrim t, Bits t) => !(Term t) -> UTerm t
  UShiftBitsTerm :: (SupportedPrim t, Bits t) => !(Term t) -> {-# UNPACK #-} !Int -> UTerm t
  URotateBitsTerm :: (SupportedPrim t, Bits t) => !(Term t) -> {-# UNPACK #-} !Int -> UTerm t
  UBVConcatTerm ::
    ( SupportedPrim (bv a),
      SupportedPrim (bv b),
      SupportedPrim (bv c),
      KnownNat a,
      KnownNat b,
      KnownNat c,
      BVConcat (bv a) (bv b) (bv c)
    ) =>
    !(Term (bv a)) ->
    !(Term (bv b)) ->
    UTerm (bv c)
  UBVSelectTerm ::
    ( SupportedPrim (bv a),
      SupportedPrim (bv w),
      KnownNat a,
      KnownNat ix,
      KnownNat w,
      BVSelect (bv a) ix w (bv w)
    ) =>
    !(TypeRep ix) ->
    !(TypeRep w) ->
    !(Term (bv a)) ->
    UTerm (bv w)
  UBVExtendTerm ::
    ( SupportedPrim (bv a),
      SupportedPrim (bv b),
      KnownNat a,
      KnownNat b,
      KnownNat n,
      BVExtend (bv a) n (bv b)
    ) =>
    !Bool ->
    !(TypeRep n) ->
    !(Term (bv a)) ->
    UTerm (bv b)
  UTabularFuncApplyTerm ::
    ( SupportedPrim a,
      SupportedPrim b
    ) =>
    Term (a =-> b) ->
    Term a ->
    UTerm b
  UGeneralFuncApplyTerm ::
    ( SupportedPrim a,
      SupportedPrim b
    ) =>
    Term (a --> b) ->
    Term a ->
    UTerm b
  UDivIntegerTerm :: Term Integer -> Term Integer -> UTerm Integer
  UModIntegerTerm :: Term Integer -> Term Integer -> UTerm Integer

eqTypedId :: (TypeRep a, Id) -> (TypeRep b, Id) -> Bool
eqTypedId (a, i1) (b, i2) = i1 == i2 && eqTypeRepBool a b
{-# INLINE eqTypedId #-}

eqHeteroTag :: Eq a => (TypeRep a, a) -> (TypeRep b, b) -> Bool
eqHeteroTag (tpa, taga) (tpb, tagb) = eqHeteroRep tpa tpb taga tagb
{-# INLINE eqHeteroTag #-}

instance (SupportedPrim t) => Interned (Term t) where
  type Uninterned (Term t) = UTerm t
  data Description (Term t) where
    DConcTerm :: t -> Description (Term t)
    DSymbTerm :: TermSymbol -> Description (Term t)
    DUnaryTerm ::
      (Eq tag, Hashable tag) =>
      {-# UNPACK #-} !(TypeRep tag, tag) ->
      {-# UNPACK #-} !(TypeRep arg, Id) ->
      Description (Term t)
    DBinaryTerm ::
      (Eq tag, Hashable tag) =>
      {-# UNPACK #-} !(TypeRep tag, tag) ->
      {-# UNPACK #-} !(TypeRep arg1, Id) ->
      {-# UNPACK #-} !(TypeRep arg2, Id) ->
      Description (Term t)
    DTernaryTerm ::
      (Eq tag, Hashable tag) =>
      {-# UNPACK #-} !(TypeRep tag, tag) ->
      {-# UNPACK #-} !(TypeRep arg1, Id) ->
      {-# UNPACK #-} !(TypeRep arg2, Id) ->
      {-# UNPACK #-} !(TypeRep arg3, Id) ->
      Description (Term t)
    DNotTerm :: {-# UNPACK #-} !Id -> Description (Term Bool)
    DOrTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Bool)
    DAndTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Bool)
    DEqvTerm :: TypeRep args -> {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Bool)
    DITETerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DAddNumTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DUMinusNumTerm :: {-# UNPACK #-} !Id -> Description (Term t)
    DTimesNumTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DAbsNumTerm :: {-# UNPACK #-} !Id -> Description (Term t)
    DSignumNumTerm :: {-# UNPACK #-} !Id -> Description (Term t)
    DLTNumTerm :: TypeRep args -> {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Bool)
    DLENumTerm :: TypeRep args -> {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Bool)
    DAndBitsTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DOrBitsTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DXorBitsTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DComplementBitsTerm :: {-# UNPACK #-} !Id -> Description (Term t)
    DShiftBitsTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Int -> Description (Term t)
    DRotateBitsTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Int -> Description (Term t)
    DBVConcatTerm :: TypeRep bv1 -> TypeRep bv2 -> {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term t)
    DBVSelectTerm ::
      forall bv (a :: Nat) (w :: Nat) (ix :: Nat).
      !(TypeRep ix) ->
      !(TypeRep (bv a), Id) ->
      Description (Term (bv w))
    DBVExtendTerm ::
      forall bv (a :: Nat) (b :: Nat) (n :: Nat).
      !Bool ->
      !(TypeRep n) ->
      {-# UNPACK #-} !(TypeRep (bv a), Id) ->
      Description (Term (bv b))
    DTabularFuncApplyTerm ::
      {-# UNPACK #-} !(TypeRep (a =-> b), Id) ->
      {-# UNPACK #-} !(TypeRep a, Id) ->
      Description (Term b)
    DGeneralFuncApplyTerm ::
      {-# UNPACK #-} !(TypeRep (a --> b), Id) ->
      {-# UNPACK #-} !(TypeRep a, Id) ->
      Description (Term b)
    DDivIntegerTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Integer)
    DModIntegerTerm :: {-# UNPACK #-} !Id -> {-# UNPACK #-} !Id -> Description (Term Integer)

  describe (UConcTerm v) = DConcTerm v
  describe ((USymbTerm name) :: UTerm t) = DSymbTerm @t name
  describe ((UUnaryTerm (tag :: tagt) (tm :: Term arg)) :: UTerm t) =
    DUnaryTerm (typeRep, tag) (typeRep :: TypeRep arg, identity tm)
  describe ((UBinaryTerm (tag :: tagt) (tm1 :: Term arg1) (tm2 :: Term arg2)) :: UTerm t) =
    DBinaryTerm @tagt @arg1 @arg2 @t (typeRep, tag) (typeRep, identity tm1) (typeRep, identity tm2)
  describe ((UTernaryTerm (tag :: tagt) (tm1 :: Term arg1) (tm2 :: Term arg2) (tm3 :: Term arg3)) :: UTerm t) =
    DTernaryTerm @tagt @arg1 @arg2 @arg3 @t
      (typeRep, tag)
      (typeRep, identity tm1)
      (typeRep, identity tm2)
      (typeRep, identity tm3)
  describe (UNotTerm arg) = DNotTerm (identity arg)
  describe (UOrTerm arg1 arg2) = DOrTerm (identity arg1) (identity arg2)
  describe (UAndTerm arg1 arg2) = DAndTerm (identity arg1) (identity arg2)
  describe (UEqvTerm (arg1 :: Term arg) arg2) = DEqvTerm (typeRep :: TypeRep arg) (identity arg1) (identity arg2)
  describe (UITETerm cond (l :: Term arg) r) = DITETerm (identity cond) (identity l) (identity r)
  describe (UAddNumTerm arg1 arg2) = DAddNumTerm (identity arg1) (identity arg2)
  describe (UUMinusNumTerm arg) = DUMinusNumTerm (identity arg)
  describe (UTimesNumTerm arg1 arg2) = DTimesNumTerm (identity arg1) (identity arg2)
  describe (UAbsNumTerm arg) = DAbsNumTerm (identity arg)
  describe (USignumNumTerm arg) = DSignumNumTerm (identity arg)
  describe (ULTNumTerm (arg1 :: arg) arg2) = DLTNumTerm (typeRep :: TypeRep arg) (identity arg1) (identity arg2)
  describe (ULENumTerm (arg1 :: arg) arg2) = DLENumTerm (typeRep :: TypeRep arg) (identity arg1) (identity arg2)
  describe (UAndBitsTerm arg1 arg2) = DAndBitsTerm (identity arg1) (identity arg2)
  describe (UOrBitsTerm arg1 arg2) = DOrBitsTerm (identity arg1) (identity arg2)
  describe (UXorBitsTerm arg1 arg2) = DXorBitsTerm (identity arg1) (identity arg2)
  describe (UComplementBitsTerm arg) = DComplementBitsTerm (identity arg)
  describe (UShiftBitsTerm arg n) = DShiftBitsTerm (identity arg) n
  describe (URotateBitsTerm arg n) = DRotateBitsTerm (identity arg) n
  describe (UBVConcatTerm (arg1 :: bv1) (arg2 :: bv2)) =
    DBVConcatTerm (typeRep :: TypeRep bv1) (typeRep :: TypeRep bv2) (identity arg1) (identity arg2)
  describe (UBVSelectTerm (ix :: TypeRep ix) _ (arg :: Term arg)) =
    DBVSelectTerm ix (typeRep :: TypeRep arg, identity arg)
  describe (UBVExtendTerm signed (n :: TypeRep n) (arg :: Term arg)) =
    DBVExtendTerm signed n (typeRep :: TypeRep arg, identity arg)
  describe (UTabularFuncApplyTerm (func :: Term f) (arg :: Term a)) =
    DTabularFuncApplyTerm (typeRep :: TypeRep f, identity func) (typeRep :: TypeRep a, identity arg)
  describe (UGeneralFuncApplyTerm (func :: Term f) (arg :: Term a)) =
    DGeneralFuncApplyTerm (typeRep :: TypeRep f, identity func) (typeRep :: TypeRep a, identity arg)
  describe (UDivIntegerTerm arg1 arg2) = DDivIntegerTerm (identity arg1) (identity arg2)
  describe (UModIntegerTerm arg1 arg2) = DModIntegerTerm (identity arg1) (identity arg2)
  identify i = go
    where
      go (UConcTerm v) = ConcTerm i v
      go (USymbTerm v) = SymbTerm i v
      go (UUnaryTerm tag tm) = UnaryTerm i tag tm
      go (UBinaryTerm tag tm1 tm2) = BinaryTerm i tag tm1 tm2
      go (UTernaryTerm tag tm1 tm2 tm3) = TernaryTerm i tag tm1 tm2 tm3
      go (UNotTerm arg) = NotTerm i arg
      go (UOrTerm arg1 arg2) = OrTerm i arg1 arg2
      go (UAndTerm arg1 arg2) = AndTerm i arg1 arg2
      go (UEqvTerm arg1 arg2) = EqvTerm i arg1 arg2
      go (UITETerm cond l r) = ITETerm i cond l r
      go (UAddNumTerm arg1 arg2) = AddNumTerm i arg1 arg2
      go (UUMinusNumTerm arg) = UMinusNumTerm i arg
      go (UTimesNumTerm arg1 arg2) = TimesNumTerm i arg1 arg2
      go (UAbsNumTerm arg) = AbsNumTerm i arg
      go (USignumNumTerm arg) = SignumNumTerm i arg
      go (ULTNumTerm arg1 arg2) = LTNumTerm i arg1 arg2
      go (ULENumTerm arg1 arg2) = LENumTerm i arg1 arg2
      go (UAndBitsTerm arg1 arg2) = AndBitsTerm i arg1 arg2
      go (UOrBitsTerm arg1 arg2) = OrBitsTerm i arg1 arg2
      go (UXorBitsTerm arg1 arg2) = XorBitsTerm i arg1 arg2
      go (UComplementBitsTerm arg) = ComplementBitsTerm i arg
      go (UShiftBitsTerm arg n) = ShiftBitsTerm i arg n
      go (URotateBitsTerm arg n) = RotateBitsTerm i arg n
      go (UBVConcatTerm arg1 arg2) = BVConcatTerm i arg1 arg2
      go (UBVSelectTerm ix w arg) = BVSelectTerm i ix w arg
      go (UBVExtendTerm signed n arg) = BVExtendTerm i signed n arg
      go (UTabularFuncApplyTerm func arg) = TabularFuncApplyTerm i func arg
      go (UGeneralFuncApplyTerm func arg) = GeneralFuncApplyTerm i func arg
      go (UDivIntegerTerm arg1 arg2) = DivIntegerTerm i arg1 arg2
      go (UModIntegerTerm arg1 arg2) = ModIntegerTerm i arg1 arg2
  cache = termCache

instance (SupportedPrim t) => Eq (Description (Term t)) where
  DConcTerm (l :: tyl) == DConcTerm (r :: tyr) = cast @tyl @tyr l == Just r
  DSymbTerm ls == DSymbTerm rs = ls == rs
  DUnaryTerm (tagl :: tagl) li == DUnaryTerm (tagr :: tagr) ri = eqHeteroTag tagl tagr && eqTypedId li ri
  DBinaryTerm (tagl :: tagl) li1 li2 == DBinaryTerm (tagr :: tagr) ri1 ri2 =
    eqHeteroTag tagl tagr && eqTypedId li1 ri1 && eqTypedId li2 ri2
  DTernaryTerm (tagl :: tagl) li1 li2 li3 == DTernaryTerm (tagr :: tagr) ri1 ri2 ri3 =
    eqHeteroTag tagl tagr && eqTypedId li1 ri1 && eqTypedId li2 ri2 && eqTypedId li3 ri3
  DNotTerm li == DNotTerm ri = li == ri
  DOrTerm li1 li2 == DOrTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DAndTerm li1 li2 == DAndTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DEqvTerm lrep li1 li2 == DEqvTerm rrep ri1 ri2 = eqTypeRepBool lrep rrep && li1 == ri1 && li2 == ri2
  DITETerm lc li1 li2 == DITETerm rc ri1 ri2 = lc == rc && li1 == ri1 && li2 == ri2
  DAddNumTerm li1 li2 == DAddNumTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DUMinusNumTerm li == DUMinusNumTerm ri = li == ri
  DTimesNumTerm li1 li2 == DTimesNumTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DAbsNumTerm li == DAbsNumTerm ri = li == ri
  DSignumNumTerm li == DSignumNumTerm ri = li == ri
  DLTNumTerm lrep li1 li2 == DLTNumTerm rrep ri1 ri2 = eqTypeRepBool lrep rrep && li1 == ri1 && li2 == ri2
  DLENumTerm lrep li1 li2 == DLENumTerm rrep ri1 ri2 = eqTypeRepBool lrep rrep && li1 == ri1 && li2 == ri2
  DAndBitsTerm li1 li2 == DAndBitsTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DOrBitsTerm li1 li2 == DOrBitsTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DXorBitsTerm li1 li2 == DXorBitsTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DComplementBitsTerm li == DComplementBitsTerm ri = li == ri
  DShiftBitsTerm li ln == DShiftBitsTerm ri rn = li == ri && ln == rn
  DRotateBitsTerm li ln == DRotateBitsTerm ri rn = li == ri && ln == rn
  DBVConcatTerm lrep1 lrep2 li1 li2 == DBVConcatTerm rrep1 rrep2 ri1 ri2 =
    eqTypeRepBool lrep1 rrep1 && eqTypeRepBool lrep2 rrep2 && li1 == ri1 && li2 == ri2
  DBVSelectTerm lix li == DBVSelectTerm rix ri =
    eqTypeRepBool lix rix && eqTypedId li ri
  DBVExtendTerm lIsSigned ln li == DBVExtendTerm rIsSigned rn ri =
    lIsSigned == rIsSigned
      && eqTypeRepBool ln rn
      && eqTypedId li ri
  DTabularFuncApplyTerm lf li == DTabularFuncApplyTerm rf ri = eqTypedId lf rf && eqTypedId li ri
  DGeneralFuncApplyTerm lf li == DGeneralFuncApplyTerm rf ri = eqTypedId lf rf && eqTypedId li ri
  DDivIntegerTerm li1 li2 == DDivIntegerTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  DModIntegerTerm li1 li2 == DModIntegerTerm ri1 ri2 = li1 == ri1 && li2 == ri2
  _ == _ = False

instance (SupportedPrim t) => Hashable (Description (Term t)) where
  hashWithSalt s (DConcTerm c) = s `hashWithSalt` (0 :: Int) `hashWithSalt` c
  hashWithSalt s (DSymbTerm name) = s `hashWithSalt` (1 :: Int) `hashWithSalt` name
  hashWithSalt s (DUnaryTerm tag id1) = s `hashWithSalt` (2 :: Int) `hashWithSalt` tag `hashWithSalt` id1
  hashWithSalt s (DBinaryTerm tag id1 id2) =
    s `hashWithSalt` (3 :: Int) `hashWithSalt` tag `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DTernaryTerm tag id1 id2 id3) =
    s `hashWithSalt` (4 :: Int) `hashWithSalt` tag `hashWithSalt` id1 `hashWithSalt` id2 `hashWithSalt` id3
  hashWithSalt s (DNotTerm id1) = s `hashWithSalt` (5 :: Int) `hashWithSalt` id1
  hashWithSalt s (DOrTerm id1 id2) = s `hashWithSalt` (6 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DAndTerm id1 id2) = s `hashWithSalt` (7 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DEqvTerm rep id1 id2) =
    s
      `hashWithSalt` (8 :: Int)
      `hashWithSalt` rep
      `hashWithSalt` id1
      `hashWithSalt` id2
  hashWithSalt s (DITETerm idc id1 id2) =
    s
      `hashWithSalt` (9 :: Int)
      `hashWithSalt` idc
      `hashWithSalt` id1
      `hashWithSalt` id2
  hashWithSalt s (DAddNumTerm id1 id2) = s `hashWithSalt` (10 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DUMinusNumTerm id1) = s `hashWithSalt` (11 :: Int) `hashWithSalt` id1
  hashWithSalt s (DTimesNumTerm id1 id2) = s `hashWithSalt` (12 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DAbsNumTerm id1) = s `hashWithSalt` (13 :: Int) `hashWithSalt` id1
  hashWithSalt s (DSignumNumTerm id1) = s `hashWithSalt` (14 :: Int) `hashWithSalt` id1
  hashWithSalt s (DLTNumTerm rep id1 id2) =
    s `hashWithSalt` (15 :: Int) `hashWithSalt` rep `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DLENumTerm rep id1 id2) =
    s `hashWithSalt` (16 :: Int) `hashWithSalt` rep `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DAndBitsTerm id1 id2) = s `hashWithSalt` (17 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DOrBitsTerm id1 id2) = s `hashWithSalt` (18 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DXorBitsTerm id1 id2) = s `hashWithSalt` (19 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DComplementBitsTerm id1) = s `hashWithSalt` (20 :: Int) `hashWithSalt` id1
  hashWithSalt s (DShiftBitsTerm id1 n) = s `hashWithSalt` (21 :: Int) `hashWithSalt` id1 `hashWithSalt` n
  hashWithSalt s (DRotateBitsTerm id1 n) = s `hashWithSalt` (22 :: Int) `hashWithSalt` id1 `hashWithSalt` n
  hashWithSalt s (DBVConcatTerm rep1 rep2 id1 id2) =
    s `hashWithSalt` (23 :: Int) `hashWithSalt` rep1 `hashWithSalt` rep2 `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DBVSelectTerm ix id1) = s `hashWithSalt` (24 :: Int) `hashWithSalt` ix `hashWithSalt` id1
  hashWithSalt s (DBVExtendTerm signed n id1) =
    s
      `hashWithSalt` (25 :: Int)
      `hashWithSalt` signed
      `hashWithSalt` n
      `hashWithSalt` id1
  hashWithSalt s (DTabularFuncApplyTerm id1 id2) = s `hashWithSalt` (26 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DGeneralFuncApplyTerm id1 id2) = s `hashWithSalt` (27 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DDivIntegerTerm id1 id2) = s `hashWithSalt` (28 :: Int) `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DModIntegerTerm id1 id2) = s `hashWithSalt` (29 :: Int) `hashWithSalt` id1 `hashWithSalt` id2

-- Basic Bool
defaultValueForBool :: Bool
defaultValueForBool = False

defaultValueForBoolDyn :: ModelValue
defaultValueForBoolDyn = toModelValue defaultValueForBool

instance SupportedPrim Bool where
  pformatConc True = "true"
  pformatConc False = "false"
  defaultValue = defaultValueForBool
  defaultValueDynamic _ = defaultValueForBoolDyn

defaultValueForInteger :: Integer
defaultValueForInteger = 0

defaultValueForIntegerDyn :: ModelValue
defaultValueForIntegerDyn = toModelValue defaultValueForInteger

-- Basic Integer
instance SupportedPrim Integer where
  pformatConc i = show i ++ "I"
  defaultValue = defaultValueForInteger
  defaultValueDynamic _ = defaultValueForIntegerDyn

-- Signed BV
instance (KnownNat w, 1 <= w) => SupportedPrim (IntN w) where
  type PrimConstraint (IntN w) = (KnownNat w, 1 <= w)
  pformatConc i = show i
  defaultValue = 0

-- Unsigned BV
instance (KnownNat w, 1 <= w) => SupportedPrim (WordN w) where
  type PrimConstraint (WordN w) = (KnownNat w, 1 <= w)
  pformatConc i = show i
  defaultValue = 0

data FuncArg = FuncArg deriving (Show, Eq, Generic, Ord, Lift, Hashable, NFData)

data (-->) a b where
  GeneralFunc :: (SupportedPrim a, SupportedPrim b) => TypeRep a -> Symbol -> Term b -> a --> b

infixr 0 -->

instance Eq (a --> b) where
  GeneralFunc _ sym1 tm1 == GeneralFunc _ sym2 tm2 = sym1 == sym2 && tm1 == tm2

instance Show (a --> b) where
  show (GeneralFunc ta sym tm) = "\\(" ++ show (TermSymbol ta sym) ++ ") -> " ++ pformat tm

instance Lift (a --> b) where
  liftTyped (GeneralFunc _ sym tm) = [||GeneralFunc (typeRep @a) sym tm||]

instance Hashable (a --> b) where
  s `hashWithSalt` (GeneralFunc _ sym tm) = s `hashWithSalt` sym `hashWithSalt` tm

instance NFData (a --> b) where
  rnf (GeneralFunc p sym tm) = rnf (SomeTypeRep p) `seq` rnf sym `seq` rnf tm

instance (SupportedPrim a, SupportedPrim b) => SupportedPrim (a --> b) where
  type PrimConstraint (a --> b) = (SupportedPrim a, SupportedPrim b)
  defaultValue = GeneralFunc typeRep (WithInfo (SimpleSymbol "a") FuncArg) (concTerm defaultValue)

instance (SupportedPrim a, SupportedPrim b) => Function (a --> b) where
  type Arg (a --> b) = Term a
  type Ret (a --> b) = Term b
  (GeneralFunc ta arg tm) # v = generalFuncSubst (TermSymbol ta arg) v tm
