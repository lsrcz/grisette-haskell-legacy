{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.SymGen
  ( SymGenState,
    SymGen (..),
    genSym,
    SymGenSimple (..),
    genSymSimple,
    SymGenNoSpec (..),
    SymGenSimpleNoSpec (..),
    genSymIndexedWithDerivedNoSpec,
    genSymSimpleIndexedWithDerivedNoSpec,
    genSymIndexedWithDerivedSameShape,
    choose,
    simpleChoose,
    chooseU,
    runSymGenIndexed,
    runSymGenIndexed',
    ListSpec (..),
    SimpleListSpec (..),
  )
where

import Control.Monad.Except
import Control.Monad.State
import qualified Control.Monad.State.Strict as S
import Control.Monad.Trans.Maybe
import Generics.Deriving
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Grisette.Data.Functor
import Grisette.Data.UnionBase

type SymGenState = (Int, String)

runSymGenIndexed :: State (Int, String) a -> String -> a
runSymGenIndexed st s = evalState st (0, s)

runSymGenIndexed' :: S.State (Int, String) a -> String -> a
runSymGenIndexed' st s = S.evalState st (0, s)

class (SymBoolOp bool, Mergeable bool a) => SymGen bool spec a where
  genSymIndexed :: (MonadState SymGenState m) => spec -> m (UnionMBase bool a)
  default genSymIndexed ::
    (SymGenSimple bool spec a) =>
    (MonadState SymGenState m) =>
    spec ->
    m (UnionMBase bool a)
  genSymIndexed spec = mrgSingle <$> genSymSimpleIndexed @bool spec

genSym :: (SymGen bool spec a) => spec -> String -> UnionMBase bool a
genSym spec name = evalState (genSymIndexed spec) (0, name)

class SymGen bool spec a => SymGenSimple bool spec a where
  genSymSimpleIndexed :: (MonadState SymGenState m) => spec -> m a

genSymSimple :: forall bool spec a. (SymGenSimple bool spec a) => spec -> String -> a
genSymSimple spec name = evalState (genSymSimpleIndexed @bool spec) (0, name)

class SymGenNoSpec bool a where
  genSymIndexedNoSpec :: (MonadState SymGenState m) => m (UnionMBase bool (a c))

instance (SymBoolOp bool) => SymGenNoSpec bool U1 where
  genSymIndexedNoSpec = return $ single U1

instance (SymBoolOp bool, SymGen bool () c) => SymGenNoSpec bool (K1 i c) where
  genSymIndexedNoSpec = fmap K1 <$> genSymIndexed ()

instance (SymBoolOp bool, SymGenNoSpec bool a) => SymGenNoSpec bool (M1 i c a) where
  genSymIndexedNoSpec = fmap M1 <$> genSymIndexedNoSpec

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenNoSpec bool a, SymGenNoSpec bool b) =>
  SymGenNoSpec bool (a :+: b)
  where
  genSymIndexedNoSpec = do
    cond :: bool <- genSymSimpleIndexed @bool ()
    l :: UnionMBase bool (a c) <- genSymIndexedNoSpec
    r :: UnionMBase bool (b c) <- genSymIndexedNoSpec
    return $ Grisette.Data.Class.UnionOp.guard cond (fmap L1 l) (fmap R1 r)

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenNoSpec bool a, SymGenNoSpec bool b) =>
  SymGenNoSpec bool (a :*: b)
  where
  genSymIndexedNoSpec = do
    l :: UnionMBase bool (a c) <- genSymIndexedNoSpec
    r :: UnionMBase bool (b c) <- genSymIndexedNoSpec
    return $ do
      l1 <- l
      r1 <- r
      return $ l1 :*: r1

-- Never use on recursive types
genSymIndexedWithDerivedNoSpec ::
  forall bool a m.
  (Generic a, SymBoolOp bool, SymGenNoSpec bool (Rep a), Mergeable bool a, MonadState SymGenState m) =>
  m (UnionMBase bool a)
genSymIndexedWithDerivedNoSpec = mrgFmap to <$> genSymIndexedNoSpec @bool @(Rep a)

-- Bool
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool () Bool where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- ()
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool () () where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- Either
instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGen bool () a, Mergeable bool a, SymGen bool () b, Mergeable bool b) =>
  SymGen bool () (Either a b)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- Maybe
instance (SymBoolOp bool, SymGenSimple bool () bool, SymGen bool () a, Mergeable bool a) => SymGen bool () (Maybe a) where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- (,)
instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGen bool () a, Mergeable bool a, SymGen bool () b, Mergeable bool b) =>
  SymGen bool () (a, b)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- (,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool () a,
    Mergeable bool a,
    SymGen bool () b,
    Mergeable bool b,
    SymGen bool () c,
    Mergeable bool c
  ) =>
  SymGen bool () (a, b, c)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

class SymGenSimpleNoSpec bool a where
  genSymSimpleIndexedNoSpec :: (MonadState SymGenState m) => m (a c)

instance (SymBoolOp bool) => SymGenSimpleNoSpec bool U1 where
  genSymSimpleIndexedNoSpec = return U1

instance (SymBoolOp bool, SymGenSimple bool () c) => SymGenSimpleNoSpec bool (K1 i c) where
  genSymSimpleIndexedNoSpec = K1 <$> genSymSimpleIndexed @bool ()

instance (SymBoolOp bool, SymGenSimpleNoSpec bool a) => SymGenSimpleNoSpec bool (M1 i c a) where
  genSymSimpleIndexedNoSpec = M1 <$> genSymSimpleIndexedNoSpec @bool

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimpleNoSpec bool a, SymGenSimpleNoSpec bool b) =>
  SymGenSimpleNoSpec bool (a :*: b)
  where
  genSymSimpleIndexedNoSpec = do
    l :: a c <- genSymSimpleIndexedNoSpec @bool
    r :: b c <- genSymSimpleIndexedNoSpec @bool
    return $ l :*: r

-- Never use on recursive types
genSymSimpleIndexedWithDerivedNoSpec ::
  forall bool a m.
  (Generic a, SymBoolOp bool, SymGenSimpleNoSpec bool (Rep a), MonadState SymGenState m) =>
  m a
genSymSimpleIndexedWithDerivedNoSpec = to <$> genSymSimpleIndexedNoSpec @bool @(Rep a)

-- ()
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool () () where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b
  ) =>
  SymGenSimple bool () (a, b)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b,
    SymGenSimple bool () c,
    Mergeable bool c
  ) =>
  SymGenSimple bool () (a, b, c)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

class SymGenSameShape bool a where
  genSymSameShapeIndexed :: (MonadState SymGenState m) => a c -> m (a c)

instance (SymBoolOp bool) => SymGenSameShape bool U1 where
  genSymSameShapeIndexed _ = return U1

instance (SymBoolOp bool, SymGenSimple bool c c) => SymGenSameShape bool (K1 i c) where
  genSymSameShapeIndexed (K1 c) = K1 <$> genSymSimpleIndexed @bool c

instance (SymBoolOp bool, SymGenSameShape bool a) => SymGenSameShape bool (M1 i c a) where
  genSymSameShapeIndexed (M1 a) = M1 <$> genSymSameShapeIndexed @bool a

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSameShape bool a, SymGenSameShape bool b) =>
  SymGenSameShape bool (a :+: b)
  where
  genSymSameShapeIndexed (L1 a) = L1 <$> genSymSameShapeIndexed @bool a
  genSymSameShapeIndexed (R1 a) = R1 <$> genSymSameShapeIndexed @bool a

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSameShape bool a, SymGenSameShape bool b) =>
  SymGenSameShape bool (a :*: b)
  where
  genSymSameShapeIndexed (a :*: b) = do
    l :: a c <- genSymSameShapeIndexed @bool a
    r :: b c <- genSymSameShapeIndexed @bool b
    return $ l :*: r

-- Can be used on recursive types
genSymIndexedWithDerivedSameShape ::
  forall bool a m.
  (Generic a, SymGenSameShape bool (Rep a), MonadState SymGenState m) =>
  a ->
  m a
genSymIndexedWithDerivedSameShape a = to <$> genSymSameShapeIndexed @bool @(Rep a) (from a)

choose ::
  forall bool a m.
  (SymBoolOp bool, Mergeable bool a, SymGenSimple bool () bool, MonadState SymGenState m) =>
  a ->
  [a] ->
  m (UnionMBase bool a)
choose x [] = return $ mrgSingle x
choose x (r : rs) = do
  b <- genSymSimpleIndexed @bool ()
  res <- choose r rs
  return $ mrgGuard b (mrgSingle x) res

simpleChoose ::
  forall bool a m.
  (SymBoolOp bool, SimpleMergeable bool a, SymGenSimple bool () bool, MonadState SymGenState m) =>
  a ->
  [a] ->
  m a
simpleChoose x [] = return x
simpleChoose x (r : rs) = do
  b <- genSymSimpleIndexed @bool ()
  res <- simpleChoose @bool r rs
  return $ mrgIf @bool b x res

chooseU ::
  forall bool a m.
  (SymBoolOp bool, Mergeable bool a, SymGenSimple bool () bool, MonadState SymGenState m) =>
  UnionMBase bool a ->
  [UnionMBase bool a] ->
  m (UnionMBase bool a)
chooseU x [] = return x
chooseU x (r : rs) = do
  b <- genSymSimpleIndexed @bool ()
  res <- chooseU r rs
  return $ mrgGuard b x res

-- Bool
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool Bool Bool where
  genSymIndexed v = return $ mrgSingle v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool Bool Bool where
  genSymSimpleIndexed v = return v

-- Integer
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool Integer Integer where
  genSymIndexed v = return $ mrgSingle v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool Integer Integer where
  genSymSimpleIndexed v = return v

-- Either
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool a a,
    Mergeable bool a,
    SymGenSimple bool b b,
    Mergeable bool b
  ) =>
  SymGen bool (Either a b) (Either a b)
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool a a,
    Mergeable bool a,
    SymGenSimple bool b b,
    Mergeable bool b
  ) =>
  SymGenSimple bool (Either a b) (Either a b)
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

-- Maybe
instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGen bool (Maybe a) (Maybe a)
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGenSimple bool (Maybe a) (Maybe a)
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

-- List
instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGen bool [a] [a]
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool () a, Mergeable bool a) =>
  SymGen bool Integer [a]
  where
  genSymIndexed v = do
    l <- gl v
    let (x : xs) = reverse $ scanr (:) [] l
    choose x xs
    where
      gl :: (MonadState SymGenState m) => Integer -> m [a]
      gl v1
        | v1 <= 0 = return []
        | otherwise = do
          l <- genSymSimpleIndexed @bool ()
          r <- gl (v1 - 1)
          return $ l : r

data ListSpec spec = ListSpec
  { genListMinLength :: Integer,
    genListMaxLength :: Integer,
    genListSubSpec :: spec
  }
  deriving (Show)

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec a, Mergeable bool a) =>
  SymGen bool (ListSpec spec) [a]
  where
  genSymIndexed (ListSpec minLen maxLen subSpec) =
    if minLen < 0 || maxLen < 0 || minLen >= maxLen
      then error $ "Bad lengthes: " ++ show (minLen, maxLen)
      else do
        l <- gl maxLen
        let (x : xs) = reverse $ scanr (:) [] $ drop (fromInteger minLen) l
        choose x xs
    where
      gl :: (MonadState SymGenState m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
          l <- genSymSimpleIndexed @bool subSpec
          r <- gl (currLen - 1)
          return $ l : r

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGenSimple bool [a] [a]
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

data SimpleListSpec spec = SimpleListSpec
  { genSimpleListLength :: Integer,
    genSimpleListSubSpec :: spec
  }
  deriving (Show)

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec a, Mergeable bool a) =>
  SymGen bool (SimpleListSpec spec) [a]
  where
  genSymIndexed = fmap mrgSingle . genSymSimpleIndexed @bool

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool spec a, Mergeable bool a) =>
  SymGenSimple bool (SimpleListSpec spec) [a]
  where
  genSymSimpleIndexed (SimpleListSpec len subSpec) =
    if len < 0
      then error $ "Bad lengthes: " ++ show len
      else do
        gl len
    where
      gl :: (MonadState SymGenState m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
          l <- genSymSimpleIndexed @bool subSpec
          r <- gl (currLen - 1)
          return $ l : r

-- (,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool a a,
    Mergeable bool a,
    SymGenSimple bool b b,
    Mergeable bool b
  ) =>
  SymGen bool (a, b) (a, b)
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool a a,
    Mergeable bool a,
    SymGenSimple bool b b,
    Mergeable bool b
  ) =>
  SymGenSimple bool (a, b) (a, b)
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

-- (,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool a a,
    Mergeable bool a,
    SymGenSimple bool b b,
    Mergeable bool b,
    SymGenSimple bool c c,
    Mergeable bool c
  ) =>
  SymGen bool (a, b, c) (a, b, c)
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool a a,
    Mergeable bool a,
    SymGenSimple bool b b,
    Mergeable bool b,
    SymGenSimple bool c c,
    Mergeable bool c
  ) =>
  SymGenSimple bool (a, b, c) (a, b, c)
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

-- MaybeT
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  SymGen bool (MaybeT m a) (MaybeT m a)
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  SymGenSimple bool (MaybeT m a) (MaybeT m a)
  where
  genSymSimpleIndexed (MaybeT v) = MaybeT <$> genSymSimpleIndexed @bool v

-- ExceptT
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Either a b)) (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  SymGen bool (ExceptT a m b) (ExceptT a m b)
  where
  genSymIndexed v = mrgSingle <$> genSymSimpleIndexed @bool v

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Either a b)) (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  SymGenSimple bool (ExceptT a m b) (ExceptT a m b)
  where
  genSymSimpleIndexed (ExceptT v) = ExceptT <$> genSymSimpleIndexed @bool v

-- UnionM
instance (SymBoolOp bool, SymGen bool spec a, Mergeable bool a) => SymGen bool spec (UnionMBase bool a) where
  genSymIndexed spec = mrgSingle <$> genSymSimpleIndexed @bool spec

instance (SymBoolOp bool, SymGen bool spec a) => SymGenSimple bool spec (UnionMBase bool a) where
  genSymSimpleIndexed spec = do
    res <- genSymIndexed spec
    if not (isMerged res) then error "Not merged" else return res

instance (SymBoolOp bool, SymGen bool a a, SymGenSimple bool () bool, Mergeable bool a) =>
  SymGen bool (UnionMBase bool a) a where
  genSymIndexed spec = go (underlyingUnion $ merge spec)
    where
      go (Single x) = genSymIndexed x
      go (Guard _ _ _ t f) = mrgGuard <$> genSymSimpleIndexed @bool () <*> go t <*> go f
