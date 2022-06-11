{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FreeT where

import Control.Monad.Trans.Free
import Data.Functor.Sum
import GHC.Generics hiding ((:+:))
import Grisette
import Data.Functor.Classes
import qualified Data.Monoid
import qualified Data.Semigroup

type FreeU f a = FreeT f UnionM a

instance
  (Mergeable1 bool f) =>
  Mergeable2 bool (FreeF f)
  where
  liftMergeStrategy2 m1 m2 =
    OrderedStrategy
      ( \case
          Pure _ -> False
          Free _ -> True
      )
      ( \case
          False -> wrapMergeStrategy m1 Pure (\(Pure a) -> a)
          True -> wrapMergeStrategy (liftMergeStrategy m2) Free (\(Free a) -> a)
      )

instance
  (Mergeable1 bool f, Mergeable bool a) =>
  Mergeable1 bool (FreeF f a)
  where
  liftMergeStrategy m = liftMergeStrategy2 mergeStrategy m

instance
  (Mergeable1 bool f, Mergeable bool a, Mergeable bool b) =>
  Mergeable bool (FreeF f a b)
  where
  mergeStrategy = mergeStrategy1

instance (Mergeable1 bool f, Mergeable1 bool m) => Mergeable1 bool (FreeT f m) where
  liftMergeStrategy m = wrapMergeStrategy (liftMergeStrategy (liftMergeStrategy2 m (liftMergeStrategy m))) FreeT runFreeT

instance (Mergeable1 bool f, Mergeable1 bool m, Mergeable bool a) => Mergeable bool (FreeT f m a) where
  mergeStrategy = mergeStrategy1

instance (Mergeable1 bool f, UnionLike bool m) => SimpleMergeable1 bool (FreeT f m) where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance (Mergeable1 bool f, UnionLike bool m) => UnionLike bool (FreeT f m) where
  mergeWithStrategy s (FreeT l) = FreeT $ mergeWithStrategy (liftMergeStrategy2 s $ liftMergeStrategy s) l
  single = FreeT . single . Pure
  unionIf cond (FreeT l) (FreeT r) = FreeT $ unionIf cond l r

instance (Mergeable1 bool f, UnionLike bool m, Mergeable bool a) => SimpleMergeable bool (FreeT f m a) where
  mrgIte = mrgIf

{-
data (:+:) f g a = Inl (f a) | Inr (g a)
  deriving (Generic, Functor)

infixr 9 :+:
-}

type (:+:) = Sum

infixr 9 :+:

data Nondet k = Or k k
  deriving (Generic, Generic1, Functor)
  deriving (Mergeable bool) via (Default (Nondet k))
  deriving (Mergeable1 bool) via (Default1 Nondet)

instance Show1 Nondet where
  liftShowsPrec sp _ i (Or l r) = showsBinaryWith sp sp "Or" i l r

instance Show k => Show (Nondet k) where
  showsPrec = showsPrec1

mrgFold ::
  (SymBoolOp bool, Functor f, Mergeable bool b) =>
  (f (UnionMBase bool b) -> UnionMBase bool b) ->
  (a -> b) ->
  FreeT f (UnionMBase bool) a ->
  UnionMBase bool b
mrgFold alg gen (FreeT m) = do
  l <- m
  case l of
    Pure a -> mrgReturn $ gen a
    Free op -> alg (fmap (mrgFold alg gen) op)

handleNondet ::
  (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a) =>
  FreeT (Nondet :+: g) (UnionMBase bool) a ->
  UnionMBase bool (FreeT g (UnionMBase bool) [a])
handleNondet = mrgFold (algNondet \+/ algR1) genNondet

genNondet ::
  (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a) =>
  a ->
  FreeT g (UnionMBase bool) [a]
genNondet x = mrgReturn [x]

algNondet ::
  (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a) =>
  Nondet (UnionMBase bool (FreeT g (UnionMBase bool) [a])) ->
  UnionMBase bool (FreeT g (UnionMBase bool) [a])
algNondet (Or l r) = do
  l' <- l
  r' <- r
  mrgReturn $ do
    l'' <- l'
    r'' <- r'
    mrgReturn $ l'' ++ r''

algR1 :: forall bool g a. (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a) =>
  g (UnionMBase bool (FreeT g (UnionMBase bool) a)) -> UnionMBase bool (FreeT g (UnionMBase bool) a)
algR1 g = mrgReturn $ wrap $ getSingle <$> g

algR :: forall bool g a. (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a) =>
  g (UnionMBase bool (FreeT g (UnionMBase bool) a)) -> UnionMBase bool (FreeT g (UnionMBase bool) a)
algR t = mrgReturn m
  where
  v :: g (FreeT g (UnionMBase bool) a)
  v = FreeT . (\x -> do
    l <- x
    runFreeT l) <$> t
  m :: FreeT g (UnionMBase bool) a
  m = FreeT . mrgReturn . Free $ v

(\+/) ::
  (f (UnionMBase bool b) -> UnionMBase bool b) ->
  (g (UnionMBase bool b) -> UnionMBase bool b) ->
  ((f :+: g) (UnionMBase bool b) -> UnionMBase bool b)
(\+/) l r = \case
  InL x -> l x
  InR x -> r x

data Void k
  deriving (Generic, Generic1, Functor)
  deriving (Mergeable bool) via (Default (Void k))
  deriving (Mergeable1 bool) via (Default1 Void)

instance Show1 Void where
  liftShowsPrec _ _ _ _ = id

instance Show k => Show (Void k) where
  showsPrec = showsPrec1

handleVoid :: (SymBoolOp bool, Mergeable bool a) => FreeT Void (UnionMBase bool) a -> UnionMBase bool a
handleVoid = mrgFold undefined id

data Writer v k = Tell v k
  deriving (Generic, Generic1, Functor)
  deriving (Mergeable bool) via (Default (Writer v k))
  deriving (Mergeable1 bool) via (Default1 (Writer v))

instance Show v => Show1 (Writer v) where
  liftShowsPrec sp _ i (Tell v k) = showsBinaryWith showsPrec sp "Tell" i v k

instance (Show v, Show k) => Show (Writer v k) where
  showsPrec = showsPrec1

algWriter ::
  (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a, Mergeable bool w, Monoid w) =>
  Writer w (UnionMBase bool (FreeT g (UnionMBase bool) (w, a))) ->
  UnionMBase bool (FreeT g (UnionMBase bool) (w, a))
algWriter (Tell w1 k) = do
  k1 <- k
  mrgReturn $ k1 >>= \(w, a) -> mrgReturn (w `mappend` w1, a)

genWriter ::
  (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a, Mergeable bool w, Monoid w) =>
  a ->
  FreeT g (UnionMBase bool) (w, a)
genWriter x = mrgReturn (mempty, x)


handleWriter ::
  (SymBoolOp bool, Functor g, Mergeable1 bool g, Mergeable bool a, Mergeable bool w, Monoid w) =>
  FreeT (Writer w :+: g) (UnionMBase bool) a ->
  UnionMBase bool (FreeT g (UnionMBase bool) (w, a))
handleWriter = mrgFold (algWriter \+/ algR1) genWriter

handleSigma :: (SymBoolOp bool, Mergeable bool a) => FreeT (Nondet :+: Void) (UnionMBase bool) a -> UnionMBase bool [a]
handleSigma c = do
  l <- handleNondet c
  handleVoid l

-- | >>> show program
-- >>> show $ mrgIf (ssymb "a") program program2
-- >>> handleSigma (mrgIf (ssymb "a") program program2)
-- >>> handleNondet (mrgIf (ssymb "a") program program2)
-- "FreeT (UMrg (Single (Free (InL (Or (FreeT (UMrg (Single (Pure 1)))) (FreeT (UMrg (Single (Pure 2)))))))))"
-- "FreeT (UMrg (Single (Free (InL (Or (FreeT (UMrg (If a (Single (Pure 1)) (Single (Pure 3))))) (FreeT (UMrg (Single (Pure 2)))))))))"
-- UMrg (If a (Single [1,2]) (Single [3,2]))
-- UMrg (Single (FreeT (UMrg (If a (Single (Pure [1,2])) (Single (Pure [3,2]))))))
program :: FreeT (Nondet :+: Void) UnionM Int
program = FreeT $ mrgReturn $ Free $ (InL $ Or (mrgReturn 1) (mrgReturn 2))

program2 :: FreeT (Nondet :+: Void) UnionM Int
program2 = FreeT $ mrgReturn $ Free $ (InL $ Or (mrgReturn 3) (mrgReturn 2))

-- | >>> show program3
-- "FreeT (UMrg (Single (Free (InL (Or (FreeT (UAny (Single (Free (InL (Or (FreeT (UMrg (Single (Pure 4)))) (FreeT (UMrg (Single (Pure 3)))))))))) (FreeT (UAny (Single (Free (InL (Or (FreeT (UMrg (Single (Pure 5)))) (FreeT (UMrg (Single (Pure 4)))))))))))))))"
-- >>> handleNondet program3
-- UMrg (Single (FreeT (UMrg (Single (Pure [4,3,5,4])))))
-- >>> show $ mrgIf (ssymb "a") program3 program4
-- "FreeT (UMrg (Single (Free (InL (Or (FreeT (UMrg (Single (Free (InL (Or (FreeT (UMrg (Single (Pure 4)))) (FreeT (UMrg (If a (Single (Pure 3)) (Single (Pure 5))))))))))) (FreeT (UMrg (Single (Free (InL (Or (FreeT (UMrg (If (! a) (Single (Pure 3)) (Single (Pure 5))))) (FreeT (UMrg (Single (Pure 4)))))))))))))))"
-- >>> show $ merge $ getSingle $ handleNondet $ mrgIf (ssymb "a") program3 program4
-- "FreeT (UMrg (If a (Single (Pure [4,3,5,4])) (If (! a) (Single (Pure [4,5,3,4])) (Single (Pure [4,5,5,4])))))"

program3 :: FreeT (Nondet :+: Void) UnionM Int
program3 = merge $ do
  a <- program
  b <- program2
  mrgReturn $ a + b

program4 :: FreeT (Nondet :+: Void) UnionM Int
program4 = merge $ do
  a <- program2
  b <- program
  mrgReturn $ a + b

instance Mergeable bool a => Mergeable bool (Data.Semigroup.Max a) where
  mergeStrategy = wrapMergeStrategy mergeStrategy Data.Semigroup.Max Data.Semigroup.getMax

instance (SymBoolOp bool, Mergeable bool x, Semigroup x) => Semigroup (UnionMBase bool x) where
  a <> b = do
    la <- a
    lb <- b
    mrgReturn $ la <> lb

instance (SymBoolOp bool, Mergeable bool x, Monoid x) => Monoid (UnionMBase bool x) where
  mempty = mrgReturn mempty

w :: Int -> FreeT (Writer (UnionM (Data.Monoid.Sum Int)) :+: Writer (UnionM (Data.Semigroup.Max Int)) :+: Void) UnionM Int
w a = FreeT $ mrgReturn $ Free $ InL (Tell (mrgReturn (Data.Monoid.Sum a)) (mrgReturn a))

w2 :: Int -> FreeT (Writer (UnionM (Data.Monoid.Sum Int)) :+: Writer (UnionM (Data.Semigroup.Max Int)) :+: Void) UnionM Int
w2 a = FreeT $ mrgReturn $ Free $ InR $ InL (Tell (mrgReturn (Data.Semigroup.Max a)) (mrgReturn a))

-- | >>> mrgIf (ssymb "a") (w1 2) (w2 2)
-- FreeT (UMrg (If a (Single (Free (InL (Tell (UMrg (Single (Sum {getSum = 3}))) (FreeT (UAny (Single (Free (InR (InL (Tell (UMrg (Single (Max {getMax = 2}))) (FreeT (UMrg (Single (Free (InL (Tell (UMrg (Single (Sum {getSum = 204}))) (FreeT (UMrg (Single (Pure 204))))))))))))))))))))) (Single (Free (InR (InL (Tell (UMrg (Single (Max {getMax = 2}))) (FreeT (UMrg (Single (Pure 2)))))))))))
-- >>> handleWriter $ mrgIf (ssymb "a") (w1 2) (w2 2)
-- UMrg (Single (FreeT (UMrg (Single (Free (InL (Tell (UMrg (Single (Max {getMax = 2}))) (FreeT (UMrg (If (! a) (Single (Pure (UMrg (Single (Sum {getSum = 0})),2))) (Single (Pure (UMrg (Single (Sum {getSum = 207})),204)))))))))))))
w1 a = do
  a1 <- w (a + 1)
  a2 <- w2 a
  w $ a + 2 + max 200 (max a1 a2)

w3 a = do
  a1 <- w (a + 1)
  a2 <- w2 a
  w $ a + 2 + max 200 (max a1 a2)

-- >>> w4
w4 = do
  a <- mrgIf (ssymb "a") (w 1) (w1 2)
  w3 (-1000)
