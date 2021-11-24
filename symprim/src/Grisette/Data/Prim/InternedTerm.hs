{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Grisette.Data.Prim.InternedTerm
  ( UnaryOp (..),
    BinaryOp (..),
    TernaryOp (..),
    Term (..),
    SupportedPrim (..),
    castTerm,
    identity,
    pformat,
    constructUnary,
    constructBinary,
    constructTernary,
    concTerm,
    symbTerm,
  )
where

import Data.Function (on)
import Data.Hashable (Hashable (hashWithSalt))
import Data.Interned
import Data.Typeable

class (SupportedPrim arg, SupportedPrim t) => UnaryOp tag arg t | tag arg -> t where
  partialEvalUnary :: (Typeable tag, Typeable t) => tag -> Term arg -> Term t
  pformatUnary :: Term arg -> String

class
  (SupportedPrim arg1, SupportedPrim arg2, SupportedPrim t) =>
  BinaryOp tag arg1 arg2 t
    | tag arg1 arg2 -> t
  where
  partialEvalBinary :: (Typeable tag, Typeable t) => tag -> Term arg1 -> Term arg2 -> Term t
  pformatBinary :: Term arg1 -> Term arg2 -> String

class
  (SupportedPrim arg1, SupportedPrim arg2, SupportedPrim arg3, SupportedPrim t) =>
  TernaryOp tag arg1 arg2 arg3 t
    | tag arg1 arg2 arg3 -> t
  where
  partialEvalTernary :: (Typeable tag, Typeable t) => tag -> Term arg1 -> Term arg2 -> Term arg3 -> Term t
  pformatTernary :: Term arg1 -> Term arg2 -> Term arg3 -> String

data Term t where
  ConcTerm :: (Typeable t, Hashable t, Eq t, Show t) => {-# UNPACK #-} !Id -> !t -> Term t
  SymbTerm :: (Typeable t) => {-# UNPACK #-} !Id -> !String -> Term t
  UnaryTerm ::
    (UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg) ->
    Term t
  BinaryTerm ::
    (BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    Term t
  TernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    !(Term arg3) ->
    Term t

instance Show (Term ty) where
  show (ConcTerm i v) = "ConcTerm{id=" ++ show i ++ ", v=" ++ show v ++ "}"
  show (SymbTerm i name) = "ShowTerm{id=" ++ show i ++ ", name=" ++ show name ++ "}"
  show (UnaryTerm i tag arg) = "Unary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg=" ++ show arg ++ "}"
  show (BinaryTerm i tag arg1 arg2) =
    "Unary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg1=" ++ show arg1
      ++ ", arg2="
      ++ show arg2
      ++ "}"
  show (TernaryTerm i tag arg1 arg2 arg3) =
    "Unary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg1=" ++ show arg1
      ++ ", arg2="
      ++ show arg2
      ++ ", arg3="
      ++ show arg3
      ++ "}"

data UTerm t where
  UConcTerm :: (Typeable t, Hashable t, Eq t, Show t) => t -> UTerm t
  USymbTerm :: (Typeable t) => String -> UTerm t
  UUnaryTerm :: (UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) => tag -> Term arg -> UTerm t
  UBinaryTerm ::
    (BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
    tag ->
    Term arg1 ->
    Term arg2 ->
    UTerm t
  UTernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
    tag ->
    Term arg1 ->
    Term arg2 ->
    Term arg3 ->
    UTerm t

class (Typeable t) => SupportedPrim t where
  termCache :: Cache (Term t)
  termCache = mkCache
  {-# NOINLINE termCache #-}
  pformatConc :: t -> String
  default pformatConc :: (Show t) => t -> String
  pformatConc = show
  pformatSymb :: String -> String
  pformatSymb = id

instance (SupportedPrim t) => Interned (Term t) where
  type Uninterned (Term t) = UTerm t
  data Description (Term t) where
    DConcTerm :: (Typeable t, Hashable t, Eq t, Show t) => t -> Description (Term t)
    DSymbTerm :: (Typeable t) => String -> Description (Term t)
    DUnaryTerm :: (UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) => tag -> Id -> Description (Term t)
    DBinaryTerm ::
      (BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
      tag ->
      Id ->
      Id ->
      Description (Term t)
    DTernaryTerm ::
      (TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
      tag ->
      Id ->
      Id ->
      Id ->
      Description (Term t)
  describe (UConcTerm v) = DConcTerm v
  describe ((USymbTerm name) :: UTerm t) = DSymbTerm @t name
  describe ((UUnaryTerm (tag :: tagt) (tm :: Term arg)) :: UTerm t) = DUnaryTerm @tagt @arg @t tag (identity tm)
  describe ((UBinaryTerm (tag :: tagt) (tm1 :: Term arg1) (tm2 :: Term arg2)) :: UTerm t) =
    DBinaryTerm @tagt @arg1 @arg2 @t tag (identity tm1) (identity tm2)
  describe ((UTernaryTerm (tag :: tagt) (tm1 :: Term arg1) (tm2 :: Term arg2) (tm3 :: Term arg3)) :: UTerm t) =
    DTernaryTerm @tagt @arg1 @arg2 @arg3 @t tag (identity tm1) (identity tm2) (identity tm3)
  identify i = go
    where
      go (UConcTerm v) = ConcTerm i v
      go (USymbTerm v) = SymbTerm i v
      go (UUnaryTerm tag tm) = UnaryTerm i tag tm
      go (UBinaryTerm tag tm1 tm2) = BinaryTerm i tag tm1 tm2
      go (UTernaryTerm tag tm1 tm2 tm3) = TernaryTerm i tag tm1 tm2 tm3
  cache = termCache

identity :: Term t -> Id
identity (ConcTerm i _) = i
identity (SymbTerm i _) = i
identity (UnaryTerm i _ _) = i
identity (BinaryTerm i _ _ _) = i
identity (TernaryTerm i _ _ _ _) = i

instance (SupportedPrim t) => Eq (Description (Term t)) where
  DConcTerm (l :: tyl) == DConcTerm (r :: tyr) = cast @tyl @tyr l == Just r
  DSymbTerm ls == DSymbTerm rs = ls == rs
  DUnaryTerm (_ :: tagl) li == DUnaryTerm (_ :: tagr) ri =
    case eqT @tagl @tagr of
      Just _ -> li == ri
      Nothing -> False
  DBinaryTerm (_ :: tagl) li1 li2 == DBinaryTerm (_ :: tagr) ri1 ri2 =
    case eqT @tagl @tagr of
      Just _ -> li1 == ri1 && li2 == ri2
      Nothing -> False
  DTernaryTerm (_ :: tagl) li1 li2 li3 == DTernaryTerm (_ :: tagr) ri1 ri2 ri3 =
    case eqT @tagl @tagr of
      Just _ -> li1 == ri1 && li2 == ri2 && li3 == ri3
      Nothing -> False
  _ == _ = False

instance (SupportedPrim t) => Hashable (Description (Term t)) where
  hashWithSalt s (DConcTerm c) = s `hashWithSalt` (0 :: Int) `hashWithSalt` c
  hashWithSalt s (DSymbTerm name) = s `hashWithSalt` (1 :: Int) `hashWithSalt` name
  hashWithSalt s (DUnaryTerm tag id1) = s `hashWithSalt` (2 :: Int) `hashWithSalt` typeOf tag `hashWithSalt` id1
  hashWithSalt s (DBinaryTerm tag id1 id2) =
    s `hashWithSalt` (3 :: Int) `hashWithSalt` typeOf tag `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DTernaryTerm tag id1 id2 id3) =
    s `hashWithSalt` (4 :: Int) `hashWithSalt` typeOf tag `hashWithSalt` id1 `hashWithSalt` id2 `hashWithSalt` id3

instance (SupportedPrim t) => Eq (Term t) where
  (==) = (==) `on` identity

instance (SupportedPrim t) => Hashable (Term t) where
  hashWithSalt s t = hashWithSalt s $ identity t

castTerm :: forall a b. (Typeable b) => Term a -> Maybe (Term b)
castTerm t@ConcTerm {} = cast t
castTerm t@SymbTerm {} = cast t
castTerm t@UnaryTerm {} = cast t
castTerm t@BinaryTerm {} = cast t
castTerm t@TernaryTerm {} = cast t

pformat :: forall t. (SupportedPrim t) => Term t -> String
pformat (ConcTerm _ t) = pformatConc t
pformat (SymbTerm _ name) = pformatSymb @t name
pformat (UnaryTerm _ (_ :: tagt) (arg1 :: Term arg1t)) = pformatUnary @tagt @arg1t @t arg1
pformat (BinaryTerm _ (_ :: tagt) (arg1 :: Term arg1t) (arg2 :: Term arg2t)) =
  pformatBinary @tagt @arg1t @arg2t @t arg1 arg2
pformat (TernaryTerm _ (_ :: tagt) (arg1 :: Term arg1t) (arg2 :: Term arg2t) (arg3 :: Term arg3t)) =
  pformatTernary @tagt @arg1t @arg2t @arg3t @t arg1 arg2 arg3

constructUnary ::
  forall tag arg t.
  (SupportedPrim t, UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg ->
  Term t
constructUnary tag tm = intern $ UUnaryTerm tag tm

constructBinary ::
  forall tag arg1 arg2 t.
  (SupportedPrim t, BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term t
constructBinary tag tm1 tm2 = intern $ UBinaryTerm tag tm1 tm2

constructTernary ::
  forall tag arg1 arg2 arg3 t.
  (SupportedPrim t, TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term arg3 ->
  Term t
constructTernary tag tm1 tm2 tm3 = intern $ UTernaryTerm tag tm1 tm2 tm3

concTerm :: (SupportedPrim t, Typeable t, Hashable t, Eq t, Show t) => t -> Term t
concTerm t = intern $ UConcTerm t

symbTerm :: (SupportedPrim t, Typeable t) => String -> Term t
symbTerm t = intern $ USymbTerm t
