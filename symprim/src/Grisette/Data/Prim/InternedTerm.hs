{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -fno-cse #-}

module Grisette.Data.Prim.InternedTerm
  ( UnaryOp (..),
    BinaryOp (..),
    TernaryOp (..),
    Term (..),
    introSupportedPrimConstraint,
    SomeTerm (..),
    SupportedPrim (..),
    Symbol (..),
    castTerm,
    identity,
    identityWithTypeRep,
    pformat,
    constructUnary,
    constructBinary,
    constructTernary,
    concTerm,
    symbTerm,
    ssymbTerm,
    isymbTerm,
    extractSymbolicsTerm,
    TermSymbol (..),
    -- termSymbolTypeRep,
  )
where

import Control.Monad.State
import Data.BitVector.Sized
import Data.BitVector.Sized.Signed
import Data.Constraint
import Data.Dynamic
import Data.Function (on)
import Data.HashMap.Strict as M
import Data.HashSet as S
import Data.Hashable (Hashable (hashWithSalt))
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Interned
import Data.Typeable
import GHC.Generics
import GHC.IO (unsafeDupablePerformIO)
import GHC.TypeNats

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

data Symbol
  = SimpleSymbol String
  | IndexedSymbol Int String
  deriving (Eq, Ord, Generic)

instance Show Symbol where
  show (SimpleSymbol str) = str
  show (IndexedSymbol i str) = str ++ "@" ++ show i

instance Hashable Symbol

data TermSymbol where
  TermSymbol :: forall t. (SupportedPrim t) => Proxy t -> Symbol -> TermSymbol

instance Eq TermSymbol where
  (TermSymbol p1 s1) == (TermSymbol p2 s2) = s1 == s2 && typeRep p1 == typeRep p2

instance Hashable TermSymbol where
  hashWithSalt s (TermSymbol p1 s1) = s `hashWithSalt` s1 `hashWithSalt` typeRep p1

instance Show TermSymbol where
  show (TermSymbol _ s) = show s

data Term t where
  ConcTerm :: (SupportedPrim t) => {-# UNPACK #-} !Id -> !t -> Term t
  SymbTerm :: (SupportedPrim t) => {-# UNPACK #-} !Id -> !TermSymbol -> Term t
  UnaryTerm ::
    (UnaryOp tag arg t, Typeable tag, Show tag) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg) ->
    Term t
  BinaryTerm ::
    (BinaryOp tag arg1 arg2 t, Typeable tag, Show tag) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    Term t
  TernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Show tag) =>
    {-# UNPACK #-} !Id ->
    !tag ->
    !(Term arg1) ->
    !(Term arg2) ->
    !(Term arg3) ->
    Term t

introSupportedPrimConstraint :: forall t a. Term t -> ((SupportedPrim t) => a) -> a
introSupportedPrimConstraint ConcTerm {} x = x
introSupportedPrimConstraint SymbTerm {} x = x
introSupportedPrimConstraint UnaryTerm {} x = x
introSupportedPrimConstraint BinaryTerm {} x = x
introSupportedPrimConstraint TernaryTerm {} x = x

data SomeTerm where
  SomeTerm :: forall a. (SupportedPrim a) => Term a -> SomeTerm

instance Show (Term ty) where
  show (ConcTerm i v) = "ConcTerm{id=" ++ show i ++ ", v=" ++ show v ++ "}"
  show (SymbTerm i name) =
    "SymbTerm{id=" ++ show i ++ ", name=" ++ show name ++ ", type="
      ++ show (typeRep (Proxy @ty))
      ++ "}"
  show (UnaryTerm i tag arg) = "Unary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg=" ++ show arg ++ "}"
  show (BinaryTerm i tag arg1 arg2) =
    "Binary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg1=" ++ show arg1
      ++ ", arg2="
      ++ show arg2
      ++ "}"
  show (TernaryTerm i tag arg1 arg2 arg3) =
    "Ternary{id=" ++ show i ++ ", tag=" ++ show tag ++ ", arg1=" ++ show arg1
      ++ ", arg2="
      ++ show arg2
      ++ ", arg3="
      ++ show arg3
      ++ "}"

data UTerm t where
  UConcTerm :: (SupportedPrim t) => t -> UTerm t
  USymbTerm :: (SupportedPrim t) => TermSymbol -> UTerm t
  UUnaryTerm :: (UnaryOp tag arg t, Typeable tag, Show tag) => tag -> Term arg -> UTerm t
  UBinaryTerm ::
    (BinaryOp tag arg1 arg2 t, Typeable tag, Show tag) =>
    tag ->
    Term arg1 ->
    Term arg2 ->
    UTerm t
  UTernaryTerm ::
    (TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Show tag) =>
    tag ->
    Term arg1 ->
    Term arg2 ->
    Term arg3 ->
    UTerm t

newDynamicCache :: forall a. (Interned a, Typeable a) => Dynamic
newDynamicCache = toDyn $ mkCache @a

termCacheCell :: IORef (M.HashMap TypeRep Dynamic)
termCacheCell = unsafeDupablePerformIO $ newIORef M.empty
{-# NOINLINE termCacheCell #-}

typeMemoizedCache :: forall a. (Interned a, Typeable a) => Cache a
typeMemoizedCache = unsafeDupablePerformIO $
  atomicModifyIORef' termCacheCell $ \m ->
    case M.lookup (typeRep (Proxy @a)) m of
      Just d -> (m, fromDyn d undefined)
      Nothing -> (M.insert (typeRep (Proxy @a)) r m, fromDyn r undefined)
        where
          !r = (newDynamicCache @a)
{-# NOINLINE typeMemoizedCache #-}

class (Typeable t, Hashable t, Eq t, Show t) => SupportedPrim t where
  type PrimConstraint t :: Constraint
  type PrimConstraint t = ()
  default withPrim :: PrimConstraint t => (PrimConstraint t => a) -> a
  withPrim :: (PrimConstraint t => a) -> a
  withPrim i = i
  termCache :: Cache (Term t)
  termCache = typeMemoizedCache
  pformatConc :: t -> String
  default pformatConc :: (Show t) => t -> String
  pformatConc = show
  pformatSymb :: Symbol -> String
  pformatSymb = show
  defaultValue :: t
  defaultValueDynamic :: Dynamic
  defaultValueDynamic = toDyn (defaultValue @t)

instance (SupportedPrim t) => Interned (Term t) where
  type Uninterned (Term t) = UTerm t
  data Description (Term t) where
    DConcTerm :: t -> Description (Term t)
    DSymbTerm :: TermSymbol -> Description (Term t)
    DUnaryTerm :: (UnaryOp tag arg t, Typeable tag, Show tag) => tag -> (TypeRep, Id) -> Description (Term t)
    DBinaryTerm ::
      (BinaryOp tag arg1 arg2 t, Typeable tag, Show tag) =>
      tag ->
      (TypeRep, Id) ->
      (TypeRep, Id) ->
      Description (Term t)
    DTernaryTerm ::
      (TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Show tag) =>
      tag ->
      (TypeRep, Id) ->
      (TypeRep, Id) ->
      (TypeRep, Id) ->
      Description (Term t)
  describe (UConcTerm v) = DConcTerm v
  describe ((USymbTerm name) :: UTerm t) = DSymbTerm @t name
  describe ((UUnaryTerm (tag :: tagt) (tm :: Term arg)) :: UTerm t) = DUnaryTerm @tagt @arg @t tag (typeRep (Proxy @arg), identity tm)
  describe ((UBinaryTerm (tag :: tagt) (tm1 :: Term arg1) (tm2 :: Term arg2)) :: UTerm t) =
    DBinaryTerm @tagt @arg1 @arg2 @t tag (typeRep (Proxy @arg1), identity tm1) (typeRep (Proxy @arg2), identity tm2)
  describe ((UTernaryTerm (tag :: tagt) (tm1 :: Term arg1) (tm2 :: Term arg2) (tm3 :: Term arg3)) :: UTerm t) =
    DTernaryTerm @tagt @arg1 @arg2 @arg3 @t tag (typeRep (Proxy @arg1), identity tm1) (typeRep (Proxy @arg2), identity tm2) (typeRep (Proxy @arg3), identity tm3)
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

identityWithTypeRep :: forall t. Term t -> (TypeRep, Id)
identityWithTypeRep (ConcTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (SymbTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (UnaryTerm i _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (BinaryTerm i _ _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (TernaryTerm i _ _ _ _) = (typeRep (Proxy @t), i)

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

instance Eq SomeTerm where
  (SomeTerm t1) == (SomeTerm t2) = identityWithTypeRep t1 == identityWithTypeRep t2

instance Hashable SomeTerm where
  hashWithSalt s (SomeTerm t) = hashWithSalt s $ identityWithTypeRep t

instance Show SomeTerm where
  show (SomeTerm t) = show t

castTerm :: forall a b. (Typeable b) => Term a -> Maybe (Term b)
castTerm t@ConcTerm {} = cast t
castTerm t@SymbTerm {} = cast t
castTerm t@UnaryTerm {} = cast t
castTerm t@BinaryTerm {} = cast t
castTerm t@TernaryTerm {} = cast t

pformat :: forall t. (SupportedPrim t) => Term t -> String
pformat (ConcTerm _ t) = pformatConc t
pformat (SymbTerm _ (TermSymbol _ symb)) = pformatSymb @t symb
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

symbTerm :: forall t. (SupportedPrim t, Typeable t) => Symbol -> Term t
symbTerm t = intern $ USymbTerm (TermSymbol (Proxy @t) t)

ssymbTerm :: (SupportedPrim t, Typeable t) => String -> Term t
ssymbTerm = symbTerm . SimpleSymbol

isymbTerm :: (SupportedPrim t, Typeable t) => Int -> String -> Term t
isymbTerm idx str = symbTerm $ IndexedSymbol idx str

extractSymbolicsSomeTerm :: SomeTerm -> S.HashSet TermSymbol
extractSymbolicsSomeTerm t1 = evalState (gocached t1) M.empty
  where
    gocached :: SomeTerm -> State (M.HashMap SomeTerm (S.HashSet TermSymbol)) (S.HashSet TermSymbol)
    gocached t = do
      v <- gets (M.lookup t)
      case v of
        Just x -> return x
        Nothing -> do
          res <- go t
          st <- get
          put $ M.insert t res st
          return res
    go :: SomeTerm -> State (M.HashMap SomeTerm (S.HashSet TermSymbol)) (S.HashSet TermSymbol)
    go (SomeTerm ConcTerm {}) = return $ S.empty
    go (SomeTerm (SymbTerm _ symb)) = return $ S.singleton symb
    go (SomeTerm (UnaryTerm _ _ arg)) = gocached (SomeTerm arg)
    go (SomeTerm (BinaryTerm _ _ arg1 arg2)) = do
      r1 <- gocached (SomeTerm arg1)
      r2 <- gocached (SomeTerm arg2)
      return $ r1 <> r2
    go (SomeTerm (TernaryTerm _ _ arg1 arg2 arg3)) = do
      r1 <- gocached (SomeTerm arg1)
      r2 <- gocached (SomeTerm arg2)
      r3 <- gocached (SomeTerm arg3)
      return $ r1 <> r2 <> r3

extractSymbolicsTerm :: (SupportedPrim a) => Term a -> S.HashSet TermSymbol
extractSymbolicsTerm t = extractSymbolicsSomeTerm (SomeTerm t)

{-
To prove that we are doing interning correctly, we ensured that:
1. For two terms with the same type t, if sub term has different type, the id must not be identical.
2. For two terms with the same type t, identical id means that same term. This could be proved by induction
  a. (Base case) concrete nodes (trivial)
  b. (Base case) symbolic nodes (trivial)
  c. (Induction) unary node. If the ids are identical, the sub-terms must have the same type (by 1).
     By the induction hypothesis, the sub-terms must be identical, then the proof is trivial.
  d. ...
  e. ...
QED
-}

-- Basic Bool
defaultValueForBool :: Bool
defaultValueForBool = True

defaultValueForBoolDyn :: Dynamic
defaultValueForBoolDyn = toDyn defaultValueForBool

instance SupportedPrim Bool where
  pformatConc True = "true"
  pformatConc False = "false"
  defaultValue = True
  defaultValueDynamic = defaultValueForBoolDyn

defaultValueForInteger :: Integer
defaultValueForInteger = 0

defaultValueForIntegerDyn :: Dynamic
defaultValueForIntegerDyn = toDyn defaultValueForInteger

-- Basic Integer
instance SupportedPrim Integer where
  pformatConc i = show i ++ "I"
  defaultValue = defaultValueForInteger
  defaultValueDynamic = defaultValueForIntegerDyn

instance (KnownNat w, 1 <= w) => Hashable (SignedBV w) where
  s `hashWithSalt` (SignedBV b) = s `hashWithSalt` b

-- Signed BV
instance (KnownNat w, 1 <= w) => SupportedPrim (SignedBV w) where
  type PrimConstraint (SignedBV w) = (KnownNat w, 1 <= w)
  pformatConc i = show i ++ "SB"
  defaultValue = mkSignedBV knownNat 0
