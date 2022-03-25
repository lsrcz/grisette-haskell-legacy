{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-cse #-}

-- {-# OPTIONS_GHC -fno-full-laziness #-}

module Grisette.Control.Monad.UnionMBase
  ( UnionMBase (..),
    IsConcrete,
    reconstructToMonadUnion,
    underlyingUnion,
    isMerged,
    (#~),
  )
where

import Control.DeepSeq
import Control.Monad.Identity (Identity (..))
import Data.Functor.Classes
import Data.Hashable
import Data.IORef
import Data.String
import GHC.IO
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Function
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.UnionOp
import Grisette.Data.Class.SymGen
import Grisette.Data.UnionBase
import Language.Haskell.TH.Syntax
import Data.MemoTrie
import Grisette.Data.MemoUtils
import qualified Data.HashMap.Lazy as HML

data UnionMBase bool a where
  UAny :: IORef (Either (UnionBase bool a) (UnionMBase bool a)) -> UnionBase bool a -> UnionMBase bool a
  UMrg :: (Mergeable bool a) => UnionBase bool a -> UnionMBase bool a

instance (SymBoolOp b, HasTrie b, HasTrie a, Mergeable b a) => HasTrie (UnionMBase b a) where
  newtype (UnionMBase b a) :->: x = UnionMBaseTrie (UnionBase b a :->: x)
  trie f = UnionMBaseTrie (trie (f . merge . freshUAny))
  untrie (UnionMBaseTrie t) = untrie t . underlyingUnion
  enumerate (UnionMBaseTrie t) = enum' (merge . freshUAny) t

instance (NFData bool, NFData a) => NFData (UnionMBase bool a) where
  rnf = rnf1

instance (NFData bool) => NFData1 (UnionMBase bool) where
  liftRnf = liftRnf2 rnf

instance NFData2 UnionMBase where
  liftRnf2 _bool _a (UAny i m) = rnf i `seq` liftRnf2 _bool _a m
  liftRnf2 _bool _a (UMrg m) = liftRnf2 _bool _a m

instance (Lift bool, Lift a) => Lift (UnionMBase bool a) where
  lift (UAny _ v) = [|freshUAny v|]
  lift (UMrg v) = [|UMrg v|]
  liftTyped = unsafeTExpCoerce . lift

freshUAny :: UnionBase bool a -> UnionMBase bool a
freshUAny v = UAny (unsafeDupablePerformIO $ newIORef $ Left v) v
{-# NOINLINE freshUAny #-}

instance (Show a, Show bool) => (Show (UnionMBase bool a)) where
  showsPrec = showsPrec1

instance (Show b) => Show1 (UnionMBase b) where
  liftShowsPrec sp sl i (UAny _ a) = showsUnaryWith (liftShowsPrec sp sl) "UAny" i a
  liftShowsPrec sp sl i (UMrg a) = showsUnaryWith (liftShowsPrec sp sl) "UMrg" i a

underlyingUnion :: UnionMBase bool a -> UnionBase bool a
underlyingUnion (UAny _ a) = a
underlyingUnion (UMrg a) = a

isMerged :: UnionMBase bool a -> Bool
isMerged UAny {} = False
isMerged UMrg {} = True

instance SymBoolOp bool => UnionOp bool (UnionMBase bool) where
  single v = (freshUAny . single) v
  guard cond (UAny _ a) (UAny _ b) = freshUAny $ guard cond a b
  guard cond (UMrg a) (UAny _ b) = UMrg $ guardWithStrategy mergeStrategy cond a b
  guard cond a (UMrg b) = UMrg $ guardWithStrategy mergeStrategy cond (underlyingUnion a) b
  singleView = singleView . underlyingUnion
  guardView (UAny _ u) = case guardView u of
    Just (c, t, f) -> Just (c, freshUAny t, freshUAny f)
    Nothing -> Nothing
  guardView (UMrg u) = case guardView u of
    Just (c, t, f) -> Just (c, UMrg t, UMrg f)
    Nothing -> Nothing
  leftMost = leftMost . underlyingUnion

instance (SymBoolOp bool) => Functor (UnionMBase bool) where
  fmap f fa = fa >>= return . f

instance (SymBoolOp bool) => Applicative (UnionMBase bool) where
  pure = single
  f <*> a = f >>= (\xf -> a >>= (return . xf))

bindUnion :: SymBoolOp bool => UnionBase bool a -> (a -> UnionMBase bool b) -> UnionMBase bool b
bindUnion (Single a') f' = f' a'
bindUnion (Guard _ _ cond ifTrue ifFalse) f' =
  guard cond (bindUnion ifTrue f') (bindUnion ifFalse f')

instance (SymBoolOp bool) => Monad (UnionMBase bool) where
  a >>= f = bindUnion (underlyingUnion a) f

instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (UnionMBase bool a) where
  mergeStrategy = SimpleStrategy $ \cond t f -> guard cond t f >>= mrgReturn @bool

instance (SymBoolOp bool, Mergeable bool a) => SimpleMergeable bool (UnionMBase bool a) where
  mrgIte = mrgIf

instance (SymBoolOp bool) => Mergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => SimpleMergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => UnionSimpleMergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => MonadUnion bool (UnionMBase bool) where
  merge m@(UMrg _) = m
  merge (UAny ref u) = unsafeDupablePerformIO $
    atomicModifyIORef' ref $ \case
      x@(Right r) -> (x, r)
      Left _ -> (Right r, r)
        where
          !r = UMrg $ fullReconstruct mergeStrategy u --m >>= mrgSingle
  {-# NOINLINE merge #-}
  mrgReturn = UMrg . single
  mrgIf (Conc c) l r = if c then merge l else merge r
  mrgIf cond l r =
    merge $ guard cond l r

instance (SymBoolOp bool, SEq bool a) => SEq bool (UnionMBase bool a) where
  x ==~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 ==~ y1

reconstructToMonadUnion :: (SymBoolOp bool, Mergeable bool a, MonadUnion bool u) => UnionMBase bool a -> u a
reconstructToMonadUnion u = go (underlyingUnion u)
  where
    go (Single v) = mrgReturn v
    go (Guard _ _ c t f) = mrgIf c (go t) (go f)

instance (SymBoolOp bool, SOrd bool a) => SOrd bool (UnionMBase bool a) where
  x <=~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 <=~ y1
  x <~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 <~ y1
  x >=~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 >=~ y1
  x >~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 >~ y1
  x `symCompare` y = reconstructToMonadUnion $ do
    x1 <- x
    y1 <- y
    x1 `symCompare` y1

instance {-# OVERLAPPABLE #-} (SymBoolOp bool, ToSym a b, Mergeable bool b) => ToSym a (UnionMBase bool b) where
  toSym = mrgReturn . toSym

instance {-# OVERLAPPING #-} (SymBoolOp bool, ToSym a b, Mergeable bool b) => ToSym (UnionMBase bool a) (UnionMBase bool b) where
  toSym = mrgFmap toSym

instance {-# OVERLAPPING #-} (SymBoolOp bool, ToSym a b, Mergeable bool b) => ToSym (Identity a) (UnionMBase bool b) where
  toSym (Identity x) = toSym x

instance (SymBoolOp bool, ToCon a b) => ToCon (UnionMBase bool a) b where
  toCon v = go $ underlyingUnion v
    where
      go (Single x) = toCon x
      go _ = Nothing

instance (SymBoolOp bool, Mergeable bool a, SymEval model a, SymEval model bool) => SymEval model (UnionMBase bool a) where
  symeval fillDefault model x = go $ underlyingUnion x
    where
      go :: UnionBase bool a -> UnionMBase bool a
      go (Single v) = mrgReturn $ symeval fillDefault model v
      go (Guard _ _ cond t f) =
        mrgIf
          (symeval fillDefault model cond)
          (go t)
          (go f)

instance
  (Monoid symbolSet, SymBoolOp bool, ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet bool) =>
  ExtractSymbolics symbolSet (UnionMBase bool a)
  where
  extractSymbolics v = go $ underlyingUnion v
    where
      go (Single x) = extractSymbolics x
      go (Guard _ _ cond t f) = extractSymbolics cond <> go t <> go f

instance (Hashable bool, Hashable a) => Hashable (UnionMBase bool a) where
  s `hashWithSalt` (UAny _ u) = s `hashWithSalt` (0 :: Int) `hashWithSalt` u
  s `hashWithSalt` (UMrg u) = s `hashWithSalt` (1 :: Int) `hashWithSalt` u

instance (Eq bool, Eq a) => Eq (UnionMBase bool a) where
  UAny _ l == UAny _ r = l == r
  UMrg l == UMrg r = l == r
  _ == _ = False

instance (Eq bool) => Eq1 (UnionMBase bool) where
  liftEq e l r = liftEq e (underlyingUnion l) (underlyingUnion r)

instance (SymBoolOp bool, Num a, Mergeable bool a) => Num (UnionMBase bool a) where
  fromInteger = mrgReturn . fromInteger
  negate x = x >>= (mrgReturn . negate)
  x + y = x >>= \x1 -> y >>= \y1 -> mrgReturn $ x1 + y1
  x - y = x >>= \x1 -> y >>= \y1 -> mrgReturn $ x1 - y1
  x * y = x >>= \x1 -> y >>= \y1 -> mrgReturn $ x1 * y1
  abs x = x >>= mrgReturn . abs
  signum x = x >>= mrgReturn . signum

instance (SymBoolOp bool, ITEOp bool a, Mergeable bool a) => ITEOp bool (UnionMBase bool a) where
  ites = mrgIf

instance (SymBoolOp bool, LogicalOp a, Mergeable bool a) => LogicalOp (UnionMBase bool a) where
  a ||~ b = do
    a1 <- a
    b1 <- b
    mrgReturn $ a1 ||~ b1
  a &&~ b = do
    a1 <- a
    b1 <- b
    mrgReturn $ a1 &&~ b1
  nots x = do
    x1 <- x
    mrgReturn $ nots x1
  xors a b = do
    a1 <- a
    b1 <- b
    mrgReturn $ a1 `xors` b1
  implies a b = do
    a1 <- a
    b1 <- b
    mrgReturn $ a1 `implies` b1

instance (SymBoolOp bool, PrimWrapper t c, Mergeable bool t) => PrimWrapper (UnionMBase bool t) c where
  conc = mrgReturn . conc
  ssymb = mrgReturn . ssymb
  isymb i s = mrgReturn $ isymb i s
  concView (SingleU (Conc b)) = Just b
  concView _ = Nothing

instance
  (SymBoolOp bool, Function f, Mergeable bool f, Mergeable bool a, Ret f ~ a) =>
  Function (UnionMBase bool f)
  where
  type Arg (UnionMBase bool f) = Arg f
  type Ret (UnionMBase bool f) = UnionMBase bool (Ret f)
  f # a = do
    f1 <- f
    mrgReturn $ f1 # a

(#~) ::
  (SymBoolOp bool, Function f, SimpleMergeable bool (Ret f)) =>
  f ->
  UnionMBase bool (Arg f) ->
  Ret f
(#~) f u = getSingle $ mrgFmap (f #) u
infixl 9 #~

instance (SymBoolOp bool, IsString a, Mergeable bool a) => IsString (UnionMBase bool a) where
  fromString = mrgReturn . fromString

{-
foldMapUnion :: (Monoid m) => (a -> m) -> UnionBase bool a -> m
foldMapUnion f (Single v) = f v
foldMapUnion f (Guard _ _ _ l r) = foldMapUnion f l <> foldMapUnion f r

instance Foldable (UnionMBase bool) where
  foldMap f u = foldMapUnion f (underlyingUnion u)

sequenceAUnion :: (Applicative m, SymBoolOp bool) => UnionBase bool (m a) -> m (UnionBase bool a)
sequenceAUnion (Single v) = single <$> v
sequenceAUnion (Guard _ _ cond l r) = guard cond <$> sequenceAUnion l <*> sequenceAUnion r

instance (SymBoolOp bool) => Traversable (UnionMBase bool) where
  sequenceA u = freshUAny <$> sequenceAUnion (underlyingUnion u)
  -}

-- SymGen
instance (SymBoolOp bool, SymGen bool spec a, Mergeable bool a) => SymGen bool spec (UnionMBase bool a) where

instance (SymBoolOp bool, SymGen bool spec a) => SymGenSimple bool spec (UnionMBase bool a) where
  genSymSimpleIndexed spec = do
    res <- genSymIndexed spec
    if not (isMerged res) then error "Not merged" else return res

instance (SymBoolOp bool, SymGen bool a a, SymGenSimple bool () bool, Mergeable bool a) =>
  SymGen bool (UnionMBase bool a) a where
  genSymIndexed spec = go (underlyingUnion $ merge spec)
    where
      go (Single x) = genSymIndexed x
      go (Guard _ _ _ t f) = mrgIf <$> genSymSimpleIndexed @bool () <*> go t <*> go f

-- Concrete Key HashMaps
class (Eq t, Ord t, Hashable t) => IsConcrete t

instance IsConcrete Bool

instance IsConcrete Integer

instance (SymBoolOp bool, IsConcrete k, Mergeable bool t) => Mergeable bool (HML.HashMap k (UnionMBase bool (Maybe t))) where
  mergeStrategy = SimpleStrategy mrgIte

instance (SymBoolOp bool, IsConcrete k, Mergeable bool t) => SimpleMergeable bool (HML.HashMap k (UnionMBase bool (Maybe t))) where
  mrgIte cond l r = 
    HML.unionWith (mrgIf cond) ul ur
    where
      ul = foldr (\k m -> case HML.lookup k m of
        Nothing -> HML.insert k (mrgReturn Nothing) m
        _ -> m
        ) l (HML.keys r)
      ur = foldr (\k m -> case HML.lookup k m of
        Nothing -> HML.insert k (mrgReturn Nothing) m
        _ -> m
        ) r (HML.keys l)

