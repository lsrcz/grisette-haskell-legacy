{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

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
    sinfosymbTerm,
    iinfosymbTerm,
    extractSymbolicsTerm,
    TermSymbol (..),
    -- termSymbolTypeRep,
    Id' (..),
    packId',
    unpackId',
    Word8List' (..),
    Word8' (..),
  )
where

import Control.DeepSeq
import Control.Monad.State
import Data.Array
import Data.BitVector.Sized
import Data.BitVector.Sized.Signed as BVS
import Data.BitVector.Sized.Unsigned as BVU
import Data.Bits
import Data.Constraint
import Data.Dynamic
import Data.Function (on)
import qualified Data.HashMap.Strict as M
import Data.HashSet as S
import Data.Hashable (Hashable (hash, hashWithSalt))
import Data.IORef (atomicModifyIORef')
import Data.Interned
import Data.Interned.Internal
import Data.Maybe
import Data.MemoTrie
import Data.Typeable
import qualified Data.Vector as V
import Data.Word
import GHC.IO (unsafeDupablePerformIO)
import GHC.TypeNats
import Grisette.Data.Prim.Caches
import Grisette.Data.Prim.ModelValue
import Grisette.Data.Prim.Orphan ()
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax.Compat

class (Lift t, Typeable t, Hashable t, Eq t, Show t, NFData t) => SupportedPrim t where
  type PrimConstraint t :: Constraint
  type PrimConstraint t = ()
  default withPrim :: PrimConstraint t => (PrimConstraint t => a) -> a
  withPrim :: (PrimConstraint t => a) -> a
  withPrim i = i
  termCache :: Cache (Term t)
  termCache = typeMemoizedCache
  termReverseCache :: ReverseCache (Term t)
  termReverseCache = typeMemoizedReverseCache
  pformatConc :: t -> String
  default pformatConc :: (Show t) => t -> String
  pformatConc = show
  pformatSymb :: Symbol -> String
  pformatSymb = show
  defaultValue :: t
  defaultValueDynamic :: ModelValue
  defaultValueDynamic = toModelValue (defaultValue @t)

class
  (SupportedPrim arg, SupportedPrim t, Lift tag, NFData tag, Show tag, Typeable tag, Eq tag, Hashable tag) =>
  UnaryOp tag arg t
    | tag arg -> t
  where
  partialEvalUnary :: (Typeable tag, Typeable t) => tag -> Term arg -> Term t
  pformatUnary :: tag -> Term arg -> String

class
  (SupportedPrim arg1, SupportedPrim arg2, SupportedPrim t, Lift tag, NFData tag, Show tag, Typeable tag, Eq tag, Hashable tag) =>
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
  IndexedSymbol :: Int -> String -> Symbol
  WithInfo :: forall a. (Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => Symbol -> a -> Symbol

-- deriving (Eq, Ord, Generic, Lift, NFData)

instance Eq Symbol where
  SimpleSymbol x == SimpleSymbol y = x == y
  IndexedSymbol i x == IndexedSymbol j y = i == j && x == y
  WithInfo s1 (i1 :: a) == WithInfo s2 (i2 :: b) = case eqT @a @b of
    Just Refl -> i1 == i2 && s1 == s2
    _ -> False
  _ == _ = False

instance Ord Symbol where
  SimpleSymbol x <= SimpleSymbol y = x <= y
  IndexedSymbol i x <= IndexedSymbol j y = i < j || (i == j && x <= y)
  WithInfo s1 (i1 :: a) <= WithInfo s2 (i2 :: b) = case eqT @a @b of
    Just Refl -> s1 < s2 || (s1 == s2 && i1 <= i2)
    _ -> False
  _ <= _ = False

instance Lift Symbol where
  liftTyped (SimpleSymbol x) = [||SimpleSymbol x||]
  liftTyped (IndexedSymbol i x) = [||IndexedSymbol i x||]
  liftTyped (WithInfo s1 i1) = [||WithInfo s1 i1||]

instance Show Symbol where
  show (SimpleSymbol str) = str
  show (IndexedSymbol i str) = str ++ "@" ++ show i
  show (WithInfo s info) = show s ++ ":" ++ show info

instance Hashable Symbol where
  s `hashWithSalt` SimpleSymbol x = s `hashWithSalt` x
  s `hashWithSalt` IndexedSymbol i x = s `hashWithSalt` i `hashWithSalt` x
  s `hashWithSalt` WithInfo sym info = s `hashWithSalt` sym `hashWithSalt` info

instance NFData Symbol where
  rnf (SimpleSymbol str) = rnf str
  rnf (IndexedSymbol i str) = rnf i `seq` rnf str
  rnf (WithInfo s info) = rnf s `seq` rnf info

data TermSymbol where
  TermSymbol :: forall t. (SupportedPrim t) => Proxy t -> Symbol -> TermSymbol

instance NFData TermSymbol where
  rnf (TermSymbol p s) = rnf p `seq` rnf s

instance Eq TermSymbol where
  (TermSymbol p1 s1) == (TermSymbol p2 s2) = s1 == s2 && typeRep p1 == typeRep p2

instance Ord TermSymbol where
  (TermSymbol p1 s1) <= (TermSymbol p2 s2) = typeRep p1 < typeRep p2 || (typeRep p1 == typeRep p2 && s1 <= s2)

instance Hashable TermSymbol where
  hashWithSalt s (TermSymbol p1 s1) = s `hashWithSalt` s1 `hashWithSalt` typeRep p1

instance Show TermSymbol where
  show (TermSymbol t s) = show s ++ " :: " ++ show (typeRep t)

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

instance NFData (Term a) where
  rnf i = identity i `seq` ()

instance Lift (Term t) where
  lift = unTypeSplice . liftTyped
  liftTyped (ConcTerm _ i) = [||concTerm i||]
  liftTyped (SymbTerm _ (TermSymbol _ sym)) = [||symbTerm sym||]
  liftTyped (UnaryTerm _ tag arg) = [||constructUnary tag arg||]
  liftTyped (BinaryTerm _ tag arg1 arg2) = [||constructBinary tag arg1 arg2||]
  liftTyped (TernaryTerm _ tag arg1 arg2 arg3) = [||constructTernary tag arg1 arg2 arg3||]

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

instance (SupportedPrim t) => Interned (Term t) where
  type Uninterned (Term t) = UTerm t
  data Description (Term t) where
    DConcTerm :: t -> Description (Term t)
    DSymbTerm :: TermSymbol -> Description (Term t)
    DUnaryTerm :: (UnaryOp tag arg t) => !tag -> (TypeRep, Id) -> Description (Term t)
    DBinaryTerm ::
      (BinaryOp tag arg1 arg2 t) =>
      tag ->
      (TypeRep, Id) ->
      (TypeRep, Id) ->
      Description (Term t)
    DTernaryTerm ::
      (TernaryOp tag arg1 arg2 arg3 t) =>
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
  DUnaryTerm (tagl :: tagl) li == DUnaryTerm (tagr :: tagr) ri =
    case eqT @tagl @tagr of
      Just Refl -> tagl == tagr && li == ri
      Nothing -> False
  DBinaryTerm (tagl :: tagl) li1 li2 == DBinaryTerm (tagr :: tagr) ri1 ri2 =
    case eqT @tagl @tagr of
      Just Refl -> tagl == tagr && li1 == ri1 && li2 == ri2
      Nothing -> False
  DTernaryTerm (tagl :: tagl) li1 li2 li3 == DTernaryTerm (tagr :: tagr) ri1 ri2 ri3 =
    case eqT @tagl @tagr of
      Just Refl -> tagl == tagr && li1 == ri1 && li2 == ri2 && li3 == ri3
      Nothing -> False
  _ == _ = False

instance (SupportedPrim t) => Hashable (Description (Term t)) where
  hashWithSalt s (DConcTerm c) = s `hashWithSalt` (0 :: Int) `hashWithSalt` c
  hashWithSalt s (DSymbTerm name) = s `hashWithSalt` (1 :: Int) `hashWithSalt` name
  hashWithSalt s (DUnaryTerm tag id1) = s `hashWithSalt` (2 :: Int) `hashWithSalt` tag `hashWithSalt` id1
  hashWithSalt s (DBinaryTerm tag id1 id2) =
    s `hashWithSalt` (3 :: Int) `hashWithSalt` tag `hashWithSalt` id1 `hashWithSalt` id2
  hashWithSalt s (DTernaryTerm tag id1 id2 id3) =
    s `hashWithSalt` (4 :: Int) `hashWithSalt` tag `hashWithSalt` id1 `hashWithSalt` id2 `hashWithSalt` id3

instance (SupportedPrim t) => Eq (Term t) where
  (==) = (==) `on` identity

instance (SupportedPrim t) => Hashable (Term t) where
  hashWithSalt s t = hashWithSalt s $ identity t

addTermToReverseCache :: forall t. (SupportedPrim t) => Term t -> IO ()
addTermToReverseCache t = addToReverseCache (identity t) t (termReverseCache @t)

findTermInReverseCache :: forall t. (SupportedPrim t) => Id -> Maybe (Term t)
findTermInReverseCache i = unsafeDupablePerformIO $ findInReverseCache i (termReverseCache @t)

word8BitWidth :: (Num a, Bits a) => a
word8BitWidth = 3

word8LevelNum :: (Num a, Bits a) => a
word8LevelNum = 1 `shiftL` word8BitWidth

newtype Word8' = Word8' Word8 deriving (Show)

instance HasTrie Word8' where
  newtype Word8' :->: x = Word8Trie' (V.Vector x)
  trie f = Word8Trie' $ V.generate word8LevelNum (f . Word8' . fromIntegral)
  untrie (Word8Trie' t) = \(Word8' w) -> V.unsafeIndex t $ fromIntegral w
  enumerate (Word8Trie' t) = [(Word8' $ fromIntegral i, V.unsafeIndex t i) | i <- [0 .. word8LevelNum -1]]

data Word8List' = W8Nil | W8Cons Word8' Word8List' deriving (Show)

instance HasTrie Word8List' where
  data Word8List' :->: x = BLTrie x (Word8' :->: (Word8List' :->: x))
  trie f = BLTrie (f W8Nil) (trie $ \w8 -> trie $ \bl -> f $ W8Cons w8 bl)
  untrie (BLTrie x t) = \case
    W8Nil -> x
    W8Cons w8 tl -> untrie (untrie t w8) tl
  enumerate (BLTrie x t) =
    (W8Nil, x) :
      [(W8Cons w8 bl, v) | (w8, tt) <- enumerate t, (bl, v) <- enumerate tt]

newtype Id' = Id' Id deriving (Show)

instance HasTrie Id' where
  newtype Id' :->: x = MTrie (Word8List' :->: x)
  trie f = MTrie $ trie (f . unpackId')
  untrie (MTrie t) = untrie t . packId'
  enumerate (MTrie t) = [(unpackId' i, v) | (i, v) <- enumerate t]

packId' :: Id' -> Word8List'
packId' (Id' i) = go $ fromIntegral i
  where
    mask = word8LevelNum - 1 :: Word
    go :: Word -> Word8List'
    go 0 = W8Nil
    go x = W8Cons (Word8' $ fromIntegral $ x .&. mask) $ go (x `shiftR` word8BitWidth)

unpackId' :: Word8List' -> Id'
unpackId' l = Id' $ fromIntegral $ go l 0 0
  where
    go :: Word8List' -> Int -> Word -> Word
    go W8Nil _ acc = acc
    go (W8Cons (Word8' x) tl) n acc = go tl (n + word8BitWidth) $ (fromIntegral x `shiftL` n) .|. acc

{-
packId' :: Id' -> Word8List'
packId' (Id' i) = go (fromIntegral i) W8Nil
  where
    mask = word8LevelNum - 1 :: Word
    go :: Word -> Word8List' -> Word8List'
    go 0 acc = acc
    go x acc = go (x `shiftR` word8BitWidth) (W8Cons (Word8' $ fromIntegral $ x .&. mask) acc)

unpackId' :: Word8List' -> Id'
unpackId' l = Id' $ fromIntegral $ go l 0
  where
    go :: Word8List' -> Word -> Word
    go W8Nil acc = acc
    go (W8Cons (Word8' x) tl) acc = go tl $ (acc `shiftL` word8BitWidth) .|. fromIntegral x
    -}

instance (SupportedPrim t) => HasTrie (Term t) where
  newtype (Term t) :->: x = TermTrie (Id' :->: x)
  trie f = TermTrie (trie $ \(Id' i) -> f (fromJust $ findTermInReverseCache i))
  untrie (TermTrie i) t = untrie i (Id' $ identity t)
  enumerate _ = error "Don't try to enumerate Terms. We implemented the MemoTrie for it with black magic" --[undefined | (i, b) <- enumerate tt]

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
pformat (UnaryTerm _ tag arg1) = pformatUnary tag arg1
pformat (BinaryTerm _ tag arg1 arg2) = pformatBinary tag arg1 arg2
pformat (TernaryTerm _ tag arg1 arg2 arg3) = pformatTernary tag arg1 arg2 arg3

internTerm :: forall t. (SupportedPrim t) => Uninterned (Term t) -> Term t
internTerm !bt = unsafeDupablePerformIO $ do
  (b, t) <- atomicModifyIORef' slot go
  when b $ addTermToReverseCache t
  {-
    atomicModifyIORef' (getReverseCache (termReverseCache @t)) $ \m ->
      (M.insert (identity t) t m, ())
      -}
  return t
  where
    slot = getCache cache ! r
    !dt = describe bt
    !hdt = hash dt
    !wid = cacheWidth dt
    r = hdt `mod` wid
    go (CacheState i m) = case M.lookup dt m of
      Nothing -> let t = identify (wid * i + r) bt in (CacheState (i + 1) (M.insert dt t m), (True, t))
      Just t -> (CacheState i m, (False, t))

constructUnary ::
  forall tag arg t.
  (SupportedPrim t, UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg ->
  Term t
constructUnary tag tm = let x = internTerm $ UUnaryTerm tag tm in x

constructBinary ::
  forall tag arg1 arg2 t.
  (SupportedPrim t, BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term t
constructBinary tag tm1 tm2 = internTerm $ UBinaryTerm tag tm1 tm2

constructTernary ::
  forall tag arg1 arg2 arg3 t.
  (SupportedPrim t, TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term arg3 ->
  Term t
constructTernary tag tm1 tm2 tm3 = internTerm $ UTernaryTerm tag tm1 tm2 tm3

concTerm :: (SupportedPrim t, Typeable t, Hashable t, Eq t, Show t) => t -> Term t
concTerm t = internTerm $ UConcTerm t

symbTerm :: forall t. (SupportedPrim t, Typeable t) => Symbol -> Term t
symbTerm t = internTerm $ USymbTerm (TermSymbol (Proxy @t) t)

ssymbTerm :: (SupportedPrim t, Typeable t) => String -> Term t
ssymbTerm = symbTerm . SimpleSymbol

isymbTerm :: (SupportedPrim t, Typeable t) => Int -> String -> Term t
isymbTerm idx str = symbTerm $ IndexedSymbol idx str

sinfosymbTerm :: (SupportedPrim t, Typeable t, Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> a -> Term t
sinfosymbTerm s info = symbTerm $ WithInfo (SimpleSymbol s) info

iinfosymbTerm :: (SupportedPrim t, Typeable t, Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => Int -> String -> a -> Term t
iinfosymbTerm idx str info = symbTerm $ WithInfo (IndexedSymbol idx str) info

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
defaultValueForBool = False

defaultValueForBoolDyn :: ModelValue
defaultValueForBoolDyn = toModelValue defaultValueForBool

instance SupportedPrim Bool where
  pformatConc True = "true"
  pformatConc False = "false"
  defaultValue = defaultValueForBool
  defaultValueDynamic = defaultValueForBoolDyn

defaultValueForInteger :: Integer
defaultValueForInteger = 0

defaultValueForIntegerDyn :: ModelValue
defaultValueForIntegerDyn = toModelValue defaultValueForInteger

-- Basic Integer
instance SupportedPrim Integer where
  pformatConc i = show i ++ "I"
  defaultValue = defaultValueForInteger
  defaultValueDynamic = defaultValueForIntegerDyn

-- Signed BV

instance (KnownNat w, 1 <= w) => SupportedPrim (SignedBV w) where
  type PrimConstraint (SignedBV w) = (KnownNat w, 1 <= w)
  pformatConc i = show i
  defaultValue = mkSignedBV knownNat 0

-- Unsigned BV
instance (KnownNat w, 1 <= w) => SupportedPrim (UnsignedBV w) where
  type PrimConstraint (UnsignedBV w) = (KnownNat w, 1 <= w)
  pformatConc i = show i
  defaultValue = mkUnsignedBV knownNat 0
