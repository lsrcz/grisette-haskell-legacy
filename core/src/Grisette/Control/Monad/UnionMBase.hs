{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-cse #-}

-- {-# OPTIONS_GHC -fno-full-laziness #-}

module Grisette.Control.Monad.UnionMBase
  ( UnionMBase (..),
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
import Grisette.Data.Functor (mrgFmap)
import Grisette.Data.UnionBase
import Language.Haskell.TH.Syntax

data UnionMBase bool a where
  UAny :: IORef (Either (UnionBase bool a) (UnionMBase bool a)) -> UnionBase bool a -> UnionMBase bool a
  UMrg :: (Mergeable bool a) => UnionBase bool a -> UnionMBase bool a

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
  mrgIf = mrgGuard

instance (SymBoolOp bool) => Mergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => SimpleMergeable1 bool (UnionMBase bool)

instance SymBoolOp bool => UnionMOp bool (UnionMBase bool) where
  merge m@(UMrg _) = m
  merge (UAny ref u) = unsafeDupablePerformIO $
    atomicModifyIORef' ref $ \case
      x@(Right r) -> (x, r)
      Left _ -> (Right r, r)
        where
          !r = UMrg $ fullReconstruct mergeStrategy u --m >>= mrgSingle
  {-# NOINLINE merge #-}
  mrgSingle = UMrg . single
  mrgGuard cond l r =
    merge $ guard cond l r

instance (SymBoolOp bool, SEq bool a, SimpleMergeable bool bool) => SEq bool (UnionMBase bool a) where
  x ==~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 ==~ y1

instance (SymBoolOp bool, SOrd bool a, SimpleMergeable bool bool) => SOrd bool (UnionMBase bool a) where
  x <=~ y = getSingle $ do
    x1 <- x
    y1 <- y
    mrgReturn $ x1 <=~ y1

instance {-# OVERLAPPABLE #-} (SymBoolOp bool, ToSym a b, Mergeable bool b) => ToSym a (UnionMBase bool b) where
  toSym = mrgSingle . toSym

instance {-# OVERLAPPING #-} (SymBoolOp bool, ToSym a b, Mergeable bool b) => ToSym (UnionMBase bool a) (UnionMBase bool b) where
  toSym = mrgFmap toSym

instance {-# OVERLAPPING #-} (SymBoolOp bool, ToSym a b, Mergeable bool b) => ToSym (Identity a) (UnionMBase bool b) where
  toSym (Identity x) = toSym x

instance (SymBoolOp bool, ToCon a b) => ToCon (UnionMBase bool a) b where
  toCon v = go $ underlyingUnion v
    where
      go (Single x) = toCon x
      go _ = Nothing

instance (SymBoolOp bool, ToCon a b, Mergeable bool b) => ToCon (UnionMBase bool a) (UnionMBase bool b) where
  toCon v = go $ underlyingUnion v
    where
      go (Single x) = mrgSingle <$> toCon x
      go (Guard _ _ cond t f) = do
        t1 <- go t
        f1 <- go f
        return $ guard cond t1 f1

instance (SymBoolOp bool, ToCon a b) => ToCon (UnionMBase bool a) (Identity b) where
  toCon v = Identity <$> (toCon v :: Maybe b)

instance (SymBoolOp bool, Mergeable bool a, SymEval model a, SymEval model bool) => SymEval model (UnionMBase bool a) where
  symeval fillDefault model x = go $ underlyingUnion x
    where
      go :: UnionBase bool a -> UnionMBase bool a
      go (Single v) = mrgSingle $ symeval fillDefault model v
      go (Guard _ _ cond t f) =
        mrgGuard
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
  l == r = underlyingUnion l == underlyingUnion r

instance (SymBoolOp bool, Num a, Mergeable bool a) => Num (UnionMBase bool a) where
  fromInteger = mrgSingle . fromInteger
  negate x = x >>= (mrgSingle . negate)
  x + y = x >>= \x1 -> y >>= \y1 -> mrgSingle $ x1 + y1
  x * y = x >>= \x1 -> y >>= \y1 -> mrgSingle $ x1 * y1
  abs x = x >>= mrgSingle . abs
  signum x = x >>= mrgSingle . signum

instance (SymBoolOp bool, ITEOp bool a, Mergeable bool a) => ITEOp bool (UnionMBase bool a) where
  ites = mrgGuard

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
  conc = mrgSingle . conc
  ssymb = mrgSingle . ssymb
  isymb i s = mrgSingle $ isymb i s
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
    mrgSingle $ f1 # a

(#~) ::
  (SymBoolOp bool, Function f, SimpleMergeable bool (Ret f)) =>
  f ->
  UnionMBase bool (Arg f) ->
  Ret f
(#~) f u = getSingle $ mrgFmap (f #) u
infixl 9 #~
