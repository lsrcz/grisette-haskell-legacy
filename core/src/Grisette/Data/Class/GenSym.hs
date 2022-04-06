{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.GenSym
  ( GenSymState,
    GenSymFresh,
    GenSymFreshT,
    genSym,
    genSymSimple,
    runGenSymFresh,
    runGenSymFreshT,
    GenSym (..),
    GenSymSimple (..),
    {-
    GenSymNoSpec (..),
    GenSymSimpleNoSpec (..),
    -}
    derivedNoSpecGenSymFresh,
    derivedNoSpecGenSymSimpleFresh,
    derivedSameShapeGenSymSimpleFresh,
    choose,
    simpleChoose,
    chooseU,
    ListSpec (..),
    SimpleListSpec (..),
    NumGenBound (..),
    NumGenUpperBound (..)
  )
where

import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Generics.Deriving
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable

type GenSymState = (Int, String)

type GenSymFresh = State GenSymState

type GenSymFreshT = StateT GenSymState

runGenSymFresh :: GenSymFresh a -> String -> a
runGenSymFresh st s = evalState st (0, s)

runGenSymFreshT :: (Monad m) => GenSymFreshT m a -> String -> m a
runGenSymFreshT st s = evalStateT st (0, s)

class (SymBoolOp bool, Mergeable bool a) => GenSym bool spec a where
  genSymFresh :: (MonadState GenSymState m, MonadUnion bool u) => spec -> m (u a)
  default genSymFresh ::
    (GenSymSimple bool spec a) =>
    (MonadState GenSymState m, MonadUnion bool u) =>
    spec ->
    m (u a)
  genSymFresh spec = mrgReturn @bool <$> genSymSimpleFresh @bool spec

genSym :: (GenSym bool spec a, MonadUnion bool u) => spec -> String -> u a
genSym = runGenSymFresh . genSymFresh

class GenSym bool spec a => GenSymSimple bool spec a where
  genSymSimpleFresh :: (MonadState GenSymState m) => spec -> m a

genSymSimple :: forall bool spec a. (GenSymSimple bool spec a) => spec -> String -> a
genSymSimple = runGenSymFresh . (genSymSimpleFresh @bool)

class GenSymNoSpec bool a where
  genSymFreshNoSpec :: (MonadState GenSymState m, MonadUnion bool u) => m (u (a c))

instance (SymBoolOp bool) => GenSymNoSpec bool U1 where
  genSymFreshNoSpec = return $ mrgReturn U1

instance (SymBoolOp bool, GenSym bool () c) => GenSymNoSpec bool (K1 i c) where
  genSymFreshNoSpec = fmap K1 <$> genSymFresh ()

instance (SymBoolOp bool, GenSymNoSpec bool a) => GenSymNoSpec bool (M1 i c a) where
  genSymFreshNoSpec = fmap M1 <$> genSymFreshNoSpec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymNoSpec bool a,
    GenSymNoSpec bool b,
    forall x. Mergeable bool (a x),
    forall x. Mergeable bool (b x)
  ) =>
  GenSymNoSpec bool (a :+: b)
  where
  genSymFreshNoSpec :: forall m u c. (MonadState GenSymState m, MonadUnion bool u) => m (u ((a :+: b) c))
  genSymFreshNoSpec = do
    cond :: bool <- genSymSimpleFresh @bool ()
    l :: u (a c) <- genSymFreshNoSpec
    r :: u (b c) <- genSymFreshNoSpec
    return $ mrgIf cond (fmap L1 l) (fmap R1 r)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymNoSpec bool a, GenSymNoSpec bool b) =>
  GenSymNoSpec bool (a :*: b)
  where
  genSymFreshNoSpec :: forall m u c. (MonadState GenSymState m, MonadUnion bool u) => m (u ((a :*: b) c))
  genSymFreshNoSpec = do
    l :: u (a c) <- genSymFreshNoSpec
    r :: u (b c) <- genSymFreshNoSpec
    return $ do
      l1 <- l
      r1 <- r
      return $ l1 :*: r1

-- Never use on recursive types
derivedNoSpecGenSymFresh ::
  forall bool a m u.
  ( Generic a,
    SymBoolOp bool,
    GenSymNoSpec bool (Rep a),
    Mergeable bool a,
    MonadState GenSymState m,
    MonadUnion bool u
  ) =>
  m (u a)
derivedNoSpecGenSymFresh = mrgFmap to <$> genSymFreshNoSpec @bool @(Rep a)

class GenSymSimpleNoSpec bool a where
  genSymSimpleFreshNoSpec :: (MonadState GenSymState m) => m (a c)

instance (SymBoolOp bool) => GenSymSimpleNoSpec bool U1 where
  genSymSimpleFreshNoSpec = return U1

instance (SymBoolOp bool, GenSymSimple bool () c) => GenSymSimpleNoSpec bool (K1 i c) where
  genSymSimpleFreshNoSpec = K1 <$> genSymSimpleFresh @bool ()

instance (SymBoolOp bool, GenSymSimpleNoSpec bool a) => GenSymSimpleNoSpec bool (M1 i c a) where
  genSymSimpleFreshNoSpec = M1 <$> genSymSimpleFreshNoSpec @bool

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimpleNoSpec bool a, GenSymSimpleNoSpec bool b) =>
  GenSymSimpleNoSpec bool (a :*: b)
  where
  genSymSimpleFreshNoSpec = do
    l :: a c <- genSymSimpleFreshNoSpec @bool
    r :: b c <- genSymSimpleFreshNoSpec @bool
    return $ l :*: r

-- Never use on recursive types
derivedNoSpecGenSymSimpleFresh ::
  forall bool a m.
  (Generic a, SymBoolOp bool, GenSymSimpleNoSpec bool (Rep a), MonadState GenSymState m) =>
  m a
derivedNoSpecGenSymSimpleFresh = to <$> genSymSimpleFreshNoSpec @bool @(Rep a)

class GenSymSameShape bool a where
  genSymSameShapeFresh :: (MonadState GenSymState m) => a c -> m (a c)

instance (SymBoolOp bool) => GenSymSameShape bool U1 where
  genSymSameShapeFresh _ = return U1

instance (SymBoolOp bool, GenSymSimple bool c c) => GenSymSameShape bool (K1 i c) where
  genSymSameShapeFresh (K1 c) = K1 <$> genSymSimpleFresh @bool c

instance (SymBoolOp bool, GenSymSameShape bool a) => GenSymSameShape bool (M1 i c a) where
  genSymSameShapeFresh (M1 a) = M1 <$> genSymSameShapeFresh @bool a

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSameShape bool a, GenSymSameShape bool b) =>
  GenSymSameShape bool (a :+: b)
  where
  genSymSameShapeFresh (L1 a) = L1 <$> genSymSameShapeFresh @bool a
  genSymSameShapeFresh (R1 a) = R1 <$> genSymSameShapeFresh @bool a

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSameShape bool a, GenSymSameShape bool b) =>
  GenSymSameShape bool (a :*: b)
  where
  genSymSameShapeFresh (a :*: b) = do
    l :: a c <- genSymSameShapeFresh @bool a
    r :: b c <- genSymSameShapeFresh @bool b
    return $ l :*: r

-- Can be used on recursive types
derivedSameShapeGenSymSimpleFresh ::
  forall bool a m.
  (Generic a, GenSymSameShape bool (Rep a), MonadState GenSymState m) =>
  a ->
  m a
derivedSameShapeGenSymSimpleFresh a = to <$> genSymSameShapeFresh @bool @(Rep a) (from a)

choose ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    GenSymSimple bool () bool,
    MonadState GenSymState m,
    MonadUnion bool u
  ) =>
  a ->
  [a] ->
  m (u a)
choose x [] = return $ mrgReturn x
choose x (r : rs) = do
  b <- genSymSimpleFresh @bool ()
  res <- choose r rs
  return $ mrgIf b (mrgReturn x) res

simpleChoose ::
  forall bool a m.
  (SymBoolOp bool, SimpleMergeable bool a, GenSymSimple bool () bool, MonadState GenSymState m) =>
  a ->
  [a] ->
  m a
simpleChoose x [] = return x
simpleChoose x (r : rs) = do
  b <- genSymSimpleFresh @bool ()
  res <- simpleChoose @bool r rs
  return $ mrgIte @bool b x res

chooseU ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    GenSymSimple bool () bool,
    MonadState GenSymState m,
    MonadUnion bool u
  ) =>
  u a ->
  [u a] ->
  m (u a)
chooseU x [] = return x
chooseU x (r : rs) = do
  b <- genSymSimpleFresh @bool ()
  res <- chooseU r rs
  return $ mrgIf b x res

-- Bool
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool Bool Bool where
  genSymFresh v = return $ mrgReturn v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool Bool Bool where
  genSymSimpleFresh v = return v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool () Bool where
  genSymFresh _ = derivedNoSpecGenSymFresh

-- Integer
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool Integer Integer where
  genSymFresh v = return $ mrgReturn v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool Integer Integer where
  genSymSimpleFresh v = return v

newtype NumGenUpperBound a = NumGenUpperBound a

data NumGenBound a = NumGenBound a a

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenUpperBound Integer) Integer where
  genSymFresh (NumGenUpperBound upperBound) =
    if upperBound < 0
      then error $ "Bad upper bound (should be >= 0): " ++ show upperBound
      else choose 0 [1 .. upperBound]

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenBound Integer) Integer where
  genSymFresh (NumGenBound l u) =
    if u < l
      then error $ "Bad bounds (upper bound should >= lower bound): " ++ show (l, u)
      else
        choose l [l + 1 .. u]

-- Char
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool Char Char where
  genSymFresh v = return $ mrgReturn v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool Char Char where
  genSymSimpleFresh v = return v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenUpperBound Char) Char where
  genSymFresh (NumGenUpperBound upperBound) = choose (toEnum 0) (toEnum <$> [1 .. fromEnum upperBound - 1])

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenBound Char) Char where
  genSymFresh (NumGenBound l u) = choose l (toEnum <$> [fromEnum l + 1 .. fromEnum u - 1])

-- Either
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool a a,
    Mergeable bool a,
    GenSymSimple bool b b,
    Mergeable bool b
  ) =>
  GenSym bool (Either a b) (Either a b)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool a a,
    Mergeable bool a,
    GenSymSimple bool b b,
    Mergeable bool b
  ) =>
  GenSymSimple bool (Either a b) (Either a b)
  where
  genSymSimpleFresh v = derivedSameShapeGenSymSimpleFresh @bool v

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSym bool () a, Mergeable bool a, GenSym bool () b, Mergeable bool b) =>
  GenSym bool () (Either a b)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

-- Maybe
instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSym bool (Maybe a) (Maybe a)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSymSimple bool (Maybe a) (Maybe a)
  where
  genSymSimpleFresh v = derivedSameShapeGenSymSimpleFresh @bool v

instance (SymBoolOp bool, GenSymSimple bool () bool, GenSym bool () a, Mergeable bool a) => GenSym bool () (Maybe a) where
  genSymFresh _ = derivedNoSpecGenSymFresh

-- List
instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool () a, Mergeable bool a) =>
  GenSym bool Integer [a]
  where
  genSymFresh v = do
    l <- gl v
    let (x : xs) = reverse $ scanr (:) [] l
    choose x xs
    where
      gl :: (MonadState GenSymState m) => Integer -> m [a]
      gl v1
        | v1 <= 0 = return []
        | otherwise = do
          l <- genSymSimpleFresh @bool ()
          r <- gl (v1 - 1)
          return $ l : r

data ListSpec spec = ListSpec
  { genListMinLength :: Integer,
    genListMaxLength :: Integer,
    genListSubSpec :: spec
  }
  deriving (Show)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec a, Mergeable bool a) =>
  GenSym bool (ListSpec spec) [a]
  where
  genSymFresh (ListSpec minLen maxLen subSpec) =
    if minLen < 0 || maxLen < 0 || minLen >= maxLen
      then error $ "Bad lengthes: " ++ show (minLen, maxLen)
      else do
        l <- gl maxLen
        let (x : xs) = drop (fromInteger minLen) $ reverse $ scanr (:) [] l
        choose x xs
    where
      gl :: (MonadState GenSymState m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
          l <- genSymSimpleFresh @bool subSpec
          r <- gl (currLen - 1)
          return $ l : r

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSym bool [a] [a]

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSymSimple bool [a] [a]
  where
  genSymSimpleFresh v = derivedSameShapeGenSymSimpleFresh @bool v

data SimpleListSpec spec = SimpleListSpec
  { genSimpleListLength :: Integer,
    genSimpleListSubSpec :: spec
  }
  deriving (Show)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec a, Mergeable bool a) =>
  GenSym bool (SimpleListSpec spec) [a]
  where
  genSymFresh = fmap mrgReturn . genSymSimpleFresh @bool

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec a, Mergeable bool a) =>
  GenSymSimple bool (SimpleListSpec spec) [a]
  where
  genSymSimpleFresh (SimpleListSpec len subSpec) =
    if len < 0
      then error $ "Bad lengthes: " ++ show len
      else do
        gl len
    where
      gl :: (MonadState GenSymState m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
          l <- genSymSimpleFresh @bool subSpec
          r <- gl (currLen - 1)
          return $ l : r

-- ()
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool () ()

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool () () where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b
  ) =>
  GenSym bool (aspec, bspec) (a, b) where
  genSymFresh (aspec, bspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    return $ do
      ax <- a1
      bx <- b1
      mrgReturn (ax, bx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b
  ) =>
  GenSymSimple bool (aspec, bspec) (a, b)
  where
  genSymSimpleFresh (aspec, bspec) =  do
    (,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSym bool () a, Mergeable bool a, GenSym bool () b, Mergeable bool b) =>
  GenSym bool () (a, b)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b
  ) =>
  GenSymSimple bool () (a, b)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c
  ) =>
  GenSym bool (aspec, bspec, cspec) (a, b, c) where
  genSymFresh (aspec, bspec, cspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      mrgReturn (ax, bx, cx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c
  ) =>
  GenSymSimple bool (aspec, bspec, cspec) (a, b, c)
  where
  genSymSimpleFresh (aspec, bspec, cspec) = do
    (,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c
  ) =>
  GenSym bool () (a, b, c)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c
  ) =>
  GenSymSimple bool () (a, b, c)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec) (a, b, c, d) where
  genSymFresh (aspec, bspec, cspec, dspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      mrgReturn (ax, bx, cx, dx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec) (a, b, c, d)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec) = do
    (,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d
  ) =>
  GenSym bool () (a, b, c, d)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d
  ) =>
  GenSymSimple bool () (a, b, c, d)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e) where
  genSymFresh (aspec, bspec, cspec, dspec, espec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      mrgReturn (ax, bx, cx, dx, ex)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec) = do
    (,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e
  ) =>
  GenSym bool () (a, b, c, d, e)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e
  ) =>
  GenSymSimple bool () (a, b, c, d, e)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e,
    GenSym bool fspec f,
    Mergeable bool f
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f) where
  genSymFresh (aspec, bspec, cspec, dspec, espec, fspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    f1 <- genSymFresh fspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      fx <- f1
      mrgReturn (ax, bx, cx, dx, ex, fx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e,
    GenSymSimple bool fspec f,
    Mergeable bool f
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec) = do
    (,,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec
      <*> genSymSimpleFresh @bool fspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e,
    GenSym bool () f,
    Mergeable bool f
  ) =>
  GenSym bool () (a, b, c, d, e, f)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e,
    GenSymSimple bool () f,
    Mergeable bool f
  ) =>
  GenSymSimple bool () (a, b, c, d, e, f)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e,
    GenSym bool fspec f,
    Mergeable bool f,
    GenSym bool gspec g,
    Mergeable bool g
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g) where
  genSymFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    f1 <- genSymFresh fspec
    g1 <- genSymFresh gspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      fx <- f1
      gx <- g1
      mrgReturn (ax, bx, cx, dx, ex, fx, gx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e,
    GenSymSimple bool fspec f,
    Mergeable bool f,
    GenSymSimple bool gspec g,
    Mergeable bool g
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    (,,,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec
      <*> genSymSimpleFresh @bool fspec
      <*> genSymSimpleFresh @bool gspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e,
    GenSym bool () f,
    Mergeable bool f,
    GenSym bool () g,
    Mergeable bool g
  ) =>
  GenSym bool () (a, b, c, d, e, f, g)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e,
    GenSymSimple bool () f,
    Mergeable bool f,
    GenSymSimple bool () g,
    Mergeable bool g
  ) =>
  GenSymSimple bool () (a, b, c, d, e, f, g)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e,
    GenSym bool fspec f,
    Mergeable bool f,
    GenSym bool gspec g,
    Mergeable bool g,
    GenSym bool hspec h,
    Mergeable bool h
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h) where
  genSymFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    f1 <- genSymFresh fspec
    g1 <- genSymFresh gspec
    h1 <- genSymFresh hspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      fx <- f1
      gx <- g1
      hx <- h1
      mrgReturn (ax, bx, cx, dx, ex, fx, gx, hx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e,
    GenSymSimple bool fspec f,
    Mergeable bool f,
    GenSymSimple bool gspec g,
    Mergeable bool g,
    GenSymSimple bool hspec h,
    Mergeable bool h
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    (,,,,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec
      <*> genSymSimpleFresh @bool fspec
      <*> genSymSimpleFresh @bool gspec
      <*> genSymSimpleFresh @bool hspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e,
    GenSym bool () f,
    Mergeable bool f,
    GenSym bool () g,
    Mergeable bool g,
    GenSym bool () h,
    Mergeable bool h
  ) =>
  GenSym bool () (a, b, c, d, e, f, g, h)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e,
    GenSymSimple bool () f,
    Mergeable bool f,
    GenSymSimple bool () g,
    Mergeable bool g,
    GenSymSimple bool () h,
    Mergeable bool h
  ) =>
  GenSymSimple bool () (a, b, c, d, e, f, g, h)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- MaybeT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSym bool spec (MaybeT m a)
  where
  genSymFresh v = do
    x <- genSymFresh @bool v
    return $ mrgFmap MaybeT x

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSymSimple bool spec (MaybeT m a)
  where
  genSymSimpleFresh v = MaybeT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSymSimple bool (MaybeT m a) (MaybeT m a)
  where
  genSymSimpleFresh (MaybeT v) = MaybeT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSym bool (MaybeT m a) (MaybeT m a)

-- ExceptT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  GenSym bool spec (ExceptT a m b)
  where
  genSymFresh v = do
    x <- genSymFresh @bool v
    return $ mrgFmap ExceptT x

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  GenSymSimple bool spec (ExceptT a m b)
  where
  genSymSimpleFresh v = ExceptT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  GenSymSimple bool (ExceptT e m a) (ExceptT e m a)
  where
  genSymSimpleFresh (ExceptT v) = ExceptT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  GenSym bool (ExceptT e m a) (ExceptT e m a)
