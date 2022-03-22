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

module Grisette.Data.Class.SymGen
  ( SymGenState,
    genSym,
    genSymSimple,
    SymGen (..),
    SymGenSimple (..),
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
    NumGenBound (..),
    NumGenUpperBound (..),
  )
where

import Control.Monad.Except
import Control.Monad.State
import qualified Control.Monad.State.Strict as S
import Control.Monad.Trans.Maybe
import Generics.Deriving
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable

type SymGenState = (Int, String)

runSymGenIndexed :: State (Int, String) a -> String -> a
runSymGenIndexed st s = evalState st (0, s)

runSymGenIndexed' :: S.State (Int, String) a -> String -> a
runSymGenIndexed' st s = S.evalState st (0, s)

class (SymBoolOp bool, Mergeable bool a) => SymGen bool spec a where
  genSymIndexed :: (MonadState SymGenState m, MonadUnion bool u) => spec -> m (u a)
  default genSymIndexed ::
    (SymGenSimple bool spec a) =>
    (MonadState SymGenState m, MonadUnion bool u) =>
    spec ->
    m (u a)
  genSymIndexed spec = mrgReturn @bool <$> genSymSimpleIndexed @bool spec

genSym :: (SymGen bool spec a, MonadUnion bool u) => spec -> String -> u a
genSym spec name = evalState (genSymIndexed spec) (0, name)

class SymGen bool spec a => SymGenSimple bool spec a where
  genSymSimpleIndexed :: (MonadState SymGenState m) => spec -> m a

genSymSimple :: forall bool spec a. (SymGenSimple bool spec a) => spec -> String -> a
genSymSimple spec name = evalState (genSymSimpleIndexed @bool spec) (0, name)

class SymGenNoSpec bool a where
  genSymIndexedNoSpec :: (MonadState SymGenState m, MonadUnion bool u) => m (u (a c))

instance (SymBoolOp bool) => SymGenNoSpec bool U1 where
  genSymIndexedNoSpec = return $ mrgReturn U1

instance (SymBoolOp bool, SymGen bool () c) => SymGenNoSpec bool (K1 i c) where
  genSymIndexedNoSpec = fmap K1 <$> genSymIndexed ()

instance (SymBoolOp bool, SymGenNoSpec bool a) => SymGenNoSpec bool (M1 i c a) where
  genSymIndexedNoSpec = fmap M1 <$> genSymIndexedNoSpec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenNoSpec bool a,
    SymGenNoSpec bool b,
    forall x. Mergeable bool (a x),
    forall x. Mergeable bool (b x)
  ) =>
  SymGenNoSpec bool (a :+: b)
  where
  genSymIndexedNoSpec :: forall m u c. (MonadState SymGenState m, MonadUnion bool u) => m (u ((a :+: b) c))
  genSymIndexedNoSpec = do
    cond :: bool <- genSymSimpleIndexed @bool ()
    l :: u (a c) <- genSymIndexedNoSpec
    r :: u (b c) <- genSymIndexedNoSpec
    return $ mrgIf cond (fmap L1 l) (fmap R1 r)

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenNoSpec bool a, SymGenNoSpec bool b) =>
  SymGenNoSpec bool (a :*: b)
  where
  genSymIndexedNoSpec :: forall m u c. (MonadState SymGenState m, MonadUnion bool u) => m (u ((a :*: b) c))
  genSymIndexedNoSpec = do
    l :: u (a c) <- genSymIndexedNoSpec
    r :: u (b c) <- genSymIndexedNoSpec
    return $ do
      l1 <- l
      r1 <- r
      return $ l1 :*: r1

-- Never use on recursive types
genSymIndexedWithDerivedNoSpec ::
  forall bool a m u.
  ( Generic a,
    SymBoolOp bool,
    SymGenNoSpec bool (Rep a),
    Mergeable bool a,
    MonadState SymGenState m,
    MonadUnion bool u
  ) =>
  m (u a)
genSymIndexedWithDerivedNoSpec = mrgFmap to <$> genSymIndexedNoSpec @bool @(Rep a)

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
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    SymGenSimple bool () bool,
    MonadState SymGenState m,
    MonadUnion bool u
  ) =>
  a ->
  [a] ->
  m (u a)
choose x [] = return $ mrgReturn x
choose x (r : rs) = do
  b <- genSymSimpleIndexed @bool ()
  res <- choose r rs
  return $ mrgIf b (mrgReturn x) res

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
  return $ mrgIte @bool b x res

chooseU ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    SymGenSimple bool () bool,
    MonadState SymGenState m,
    MonadUnion bool u
  ) =>
  u a ->
  [u a] ->
  m (u a)
chooseU x [] = return x
chooseU x (r : rs) = do
  b <- genSymSimpleIndexed @bool ()
  res <- chooseU r rs
  return $ mrgIf b x res

-- Bool
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool Bool Bool where
  genSymIndexed v = return $ mrgReturn v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool Bool Bool where
  genSymSimpleIndexed v = return v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool () Bool where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- Integer
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool Integer Integer where
  genSymIndexed v = return $ mrgReturn v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool Integer Integer where
  genSymSimpleIndexed v = return v

newtype NumGenUpperBound a = NumGenUpperBound a

data NumGenBound a = NumGenBound a a

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool (NumGenUpperBound Integer) Integer where
  genSymIndexed (NumGenUpperBound upperBound) =
    if upperBound < 0
      then error $ "Bad upper bound (should be >= 0): " ++ show upperBound
      else choose 0 [1 .. upperBound]

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool (NumGenBound Integer) Integer where
  genSymIndexed (NumGenBound l u) =
    if u < l
      then error $ "Bad bounds (upper bound should >= lower bound): " ++ show (l, u)
      else
        choose l [l + 1 .. u]

-- Char
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool Char Char where
  genSymIndexed v = return $ mrgReturn v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool Char Char where
  genSymSimpleIndexed v = return v

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool (NumGenUpperBound Char) Char where
  genSymIndexed (NumGenUpperBound upperBound) = choose (toEnum 0) (toEnum <$> [1 .. fromEnum upperBound - 1])

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool (NumGenBound Char) Char where
  genSymIndexed (NumGenBound l u) = choose l (toEnum <$> [fromEnum l + 1 .. fromEnum u - 1])

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

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGen bool () a, Mergeable bool a, SymGen bool () b, Mergeable bool b) =>
  SymGen bool () (Either a b)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- Maybe
instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGen bool (Maybe a) (Maybe a)

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGenSimple bool (Maybe a) (Maybe a)
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

instance (SymBoolOp bool, SymGenSimple bool () bool, SymGen bool () a, Mergeable bool a) => SymGen bool () (Maybe a) where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

-- List
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
        let (x : xs) = drop (fromInteger minLen) $ reverse $ scanr (:) [] l
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
  SymGen bool [a] [a]

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
  genSymIndexed = fmap mrgReturn . genSymSimpleIndexed @bool

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

-- ()
instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGen bool () ()

instance (SymBoolOp bool, SymGenSimple bool () bool) => SymGenSimple bool () () where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b
  ) =>
  SymGen bool (aspec, bspec) (a, b) where
  genSymIndexed (aspec, bspec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    return $ do
      ax <- a1
      bx <- b1
      mrgReturn (ax, bx)

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b
  ) =>
  SymGenSimple bool (aspec, bspec) (a, b)
  where
  genSymSimpleIndexed (aspec, bspec) =  do
    (,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec

instance
  (SymBoolOp bool, SymGenSimple bool () bool, SymGen bool () a, Mergeable bool a, SymGen bool () b, Mergeable bool b) =>
  SymGen bool () (a, b)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

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
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b,
    SymGen bool cspec c,
    Mergeable bool c
  ) =>
  SymGen bool (aspec, bspec, cspec) (a, b, c) where
  genSymIndexed (aspec, bspec, cspec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    c1 <- genSymIndexed cspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      mrgReturn (ax, bx, cx)

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b,
    SymGenSimple bool cspec c,
    Mergeable bool c
  ) =>
  SymGenSimple bool (aspec, bspec, cspec) (a, b, c)
  where
  genSymSimpleIndexed (aspec, bspec, cspec) = do
    (,,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec
      <*> genSymSimpleIndexed @bool cspec

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

-- (,,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b,
    SymGen bool cspec c,
    Mergeable bool c,
    SymGen bool dspec d,
    Mergeable bool d
  ) =>
  SymGen bool (aspec, bspec, cspec, dspec) (a, b, c, d) where
  genSymIndexed (aspec, bspec, cspec, dspec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    c1 <- genSymIndexed cspec
    d1 <- genSymIndexed dspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      mrgReturn (ax, bx, cx, dx)

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b,
    SymGenSimple bool cspec c,
    Mergeable bool c,
    SymGenSimple bool dspec d,
    Mergeable bool d
  ) =>
  SymGenSimple bool (aspec, bspec, cspec, dspec) (a, b, c, d)
  where
  genSymSimpleIndexed (aspec, bspec, cspec, dspec) = do
    (,,,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec
      <*> genSymSimpleIndexed @bool cspec
      <*> genSymSimpleIndexed @bool dspec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool () a,
    Mergeable bool a,
    SymGen bool () b,
    Mergeable bool b,
    SymGen bool () c,
    Mergeable bool c,
    SymGen bool () d,
    Mergeable bool d
  ) =>
  SymGen bool () (a, b, c, d)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b,
    SymGenSimple bool () c,
    Mergeable bool c,
    SymGenSimple bool () d,
    Mergeable bool d
  ) =>
  SymGenSimple bool () (a, b, c, d)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,,,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b,
    SymGen bool cspec c,
    Mergeable bool c,
    SymGen bool dspec d,
    Mergeable bool d,
    SymGen bool espec e,
    Mergeable bool e
  ) =>
  SymGen bool (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e) where
  genSymIndexed (aspec, bspec, cspec, dspec, espec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    c1 <- genSymIndexed cspec
    d1 <- genSymIndexed dspec
    e1 <- genSymIndexed espec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      mrgReturn (ax, bx, cx, dx, ex)

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b,
    SymGenSimple bool cspec c,
    Mergeable bool c,
    SymGenSimple bool dspec d,
    Mergeable bool d,
    SymGenSimple bool espec e,
    Mergeable bool e
  ) =>
  SymGenSimple bool (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e)
  where
  genSymSimpleIndexed (aspec, bspec, cspec, dspec, espec) = do
    (,,,,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec
      <*> genSymSimpleIndexed @bool cspec
      <*> genSymSimpleIndexed @bool dspec
      <*> genSymSimpleIndexed @bool espec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool () a,
    Mergeable bool a,
    SymGen bool () b,
    Mergeable bool b,
    SymGen bool () c,
    Mergeable bool c,
    SymGen bool () d,
    Mergeable bool d,
    SymGen bool () e,
    Mergeable bool e
  ) =>
  SymGen bool () (a, b, c, d, e)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b,
    SymGenSimple bool () c,
    Mergeable bool c,
    SymGenSimple bool () d,
    Mergeable bool d,
    SymGenSimple bool () e,
    Mergeable bool e
  ) =>
  SymGenSimple bool () (a, b, c, d, e)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,,,,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b,
    SymGen bool cspec c,
    Mergeable bool c,
    SymGen bool dspec d,
    Mergeable bool d,
    SymGen bool espec e,
    Mergeable bool e,
    SymGen bool fspec f,
    Mergeable bool f
  ) =>
  SymGen bool (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f) where
  genSymIndexed (aspec, bspec, cspec, dspec, espec, fspec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    c1 <- genSymIndexed cspec
    d1 <- genSymIndexed dspec
    e1 <- genSymIndexed espec
    f1 <- genSymIndexed fspec
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
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b,
    SymGenSimple bool cspec c,
    Mergeable bool c,
    SymGenSimple bool dspec d,
    Mergeable bool d,
    SymGenSimple bool espec e,
    Mergeable bool e,
    SymGenSimple bool fspec f,
    Mergeable bool f
  ) =>
  SymGenSimple bool (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f)
  where
  genSymSimpleIndexed (aspec, bspec, cspec, dspec, espec, fspec) = do
    (,,,,,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec
      <*> genSymSimpleIndexed @bool cspec
      <*> genSymSimpleIndexed @bool dspec
      <*> genSymSimpleIndexed @bool espec
      <*> genSymSimpleIndexed @bool fspec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool () a,
    Mergeable bool a,
    SymGen bool () b,
    Mergeable bool b,
    SymGen bool () c,
    Mergeable bool c,
    SymGen bool () d,
    Mergeable bool d,
    SymGen bool () e,
    Mergeable bool e,
    SymGen bool () f,
    Mergeable bool f
  ) =>
  SymGen bool () (a, b, c, d, e, f)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b,
    SymGenSimple bool () c,
    Mergeable bool c,
    SymGenSimple bool () d,
    Mergeable bool d,
    SymGenSimple bool () e,
    Mergeable bool e,
    SymGenSimple bool () f,
    Mergeable bool f
  ) =>
  SymGenSimple bool () (a, b, c, d, e, f)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,,,,,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b,
    SymGen bool cspec c,
    Mergeable bool c,
    SymGen bool dspec d,
    Mergeable bool d,
    SymGen bool espec e,
    Mergeable bool e,
    SymGen bool fspec f,
    Mergeable bool f,
    SymGen bool gspec g,
    Mergeable bool g
  ) =>
  SymGen bool (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g) where
  genSymIndexed (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    c1 <- genSymIndexed cspec
    d1 <- genSymIndexed dspec
    e1 <- genSymIndexed espec
    f1 <- genSymIndexed fspec
    g1 <- genSymIndexed gspec
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
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b,
    SymGenSimple bool cspec c,
    Mergeable bool c,
    SymGenSimple bool dspec d,
    Mergeable bool d,
    SymGenSimple bool espec e,
    Mergeable bool e,
    SymGenSimple bool fspec f,
    Mergeable bool f,
    SymGenSimple bool gspec g,
    Mergeable bool g
  ) =>
  SymGenSimple bool (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g)
  where
  genSymSimpleIndexed (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    (,,,,,,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec
      <*> genSymSimpleIndexed @bool cspec
      <*> genSymSimpleIndexed @bool dspec
      <*> genSymSimpleIndexed @bool espec
      <*> genSymSimpleIndexed @bool fspec
      <*> genSymSimpleIndexed @bool gspec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool () a,
    Mergeable bool a,
    SymGen bool () b,
    Mergeable bool b,
    SymGen bool () c,
    Mergeable bool c,
    SymGen bool () d,
    Mergeable bool d,
    SymGen bool () e,
    Mergeable bool e,
    SymGen bool () f,
    Mergeable bool f,
    SymGen bool () g,
    Mergeable bool g
  ) =>
  SymGen bool () (a, b, c, d, e, f, g)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b,
    SymGenSimple bool () c,
    Mergeable bool c,
    SymGenSimple bool () d,
    Mergeable bool d,
    SymGenSimple bool () e,
    Mergeable bool e,
    SymGenSimple bool () f,
    Mergeable bool f,
    SymGenSimple bool () g,
    Mergeable bool g
  ) =>
  SymGenSimple bool () (a, b, c, d, e, f, g)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- (,,,,,,,)
instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool aspec a,
    Mergeable bool a,
    SymGen bool bspec b,
    Mergeable bool b,
    SymGen bool cspec c,
    Mergeable bool c,
    SymGen bool dspec d,
    Mergeable bool d,
    SymGen bool espec e,
    Mergeable bool e,
    SymGen bool fspec f,
    Mergeable bool f,
    SymGen bool gspec g,
    Mergeable bool g,
    SymGen bool hspec h,
    Mergeable bool h
  ) =>
  SymGen bool (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h) where
  genSymIndexed (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    a1 <- genSymIndexed aspec
    b1 <- genSymIndexed bspec
    c1 <- genSymIndexed cspec
    d1 <- genSymIndexed dspec
    e1 <- genSymIndexed espec
    f1 <- genSymIndexed fspec
    g1 <- genSymIndexed gspec
    h1 <- genSymIndexed hspec
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
    SymGenSimple bool () bool,
    SymGenSimple bool aspec a,
    Mergeable bool a,
    SymGenSimple bool bspec b,
    Mergeable bool b,
    SymGenSimple bool cspec c,
    Mergeable bool c,
    SymGenSimple bool dspec d,
    Mergeable bool d,
    SymGenSimple bool espec e,
    Mergeable bool e,
    SymGenSimple bool fspec f,
    Mergeable bool f,
    SymGenSimple bool gspec g,
    Mergeable bool g,
    SymGenSimple bool hspec h,
    Mergeable bool h
  ) =>
  SymGenSimple bool (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h)
  where
  genSymSimpleIndexed (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    (,,,,,,,)
      <$> genSymSimpleIndexed @bool aspec
      <*> genSymSimpleIndexed @bool bspec
      <*> genSymSimpleIndexed @bool cspec
      <*> genSymSimpleIndexed @bool dspec
      <*> genSymSimpleIndexed @bool espec
      <*> genSymSimpleIndexed @bool fspec
      <*> genSymSimpleIndexed @bool gspec
      <*> genSymSimpleIndexed @bool hspec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool () a,
    Mergeable bool a,
    SymGen bool () b,
    Mergeable bool b,
    SymGen bool () c,
    Mergeable bool c,
    SymGen bool () d,
    Mergeable bool d,
    SymGen bool () e,
    Mergeable bool e,
    SymGen bool () f,
    Mergeable bool f,
    SymGen bool () g,
    Mergeable bool g,
    SymGen bool () h,
    Mergeable bool h
  ) =>
  SymGen bool () (a, b, c, d, e, f, g, h)
  where
  genSymIndexed _ = genSymIndexedWithDerivedNoSpec

instance
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool () a,
    Mergeable bool a,
    SymGenSimple bool () b,
    Mergeable bool b,
    SymGenSimple bool () c,
    Mergeable bool c,
    SymGenSimple bool () d,
    Mergeable bool d,
    SymGenSimple bool () e,
    Mergeable bool e,
    SymGenSimple bool () f,
    Mergeable bool f,
    SymGenSimple bool () g,
    Mergeable bool g,
    SymGenSimple bool () h,
    Mergeable bool h
  ) =>
  SymGenSimple bool () (a, b, c, d, e, f, g, h)
  where
  genSymSimpleIndexed _ = genSymSimpleIndexedWithDerivedNoSpec @bool

-- MaybeT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  SymGen bool spec (MaybeT m a)
  where
  genSymIndexed v = do
    x <- genSymIndexed @bool v
    return $ mrgFmap MaybeT x

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  SymGenSimple bool spec (MaybeT m a)
  where
  genSymSimpleIndexed v = MaybeT <$> genSymSimpleIndexed @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  SymGenSimple bool (MaybeT m a) (MaybeT m a)
  where
  genSymSimpleIndexed (MaybeT v) = MaybeT <$> genSymSimpleIndexed @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  SymGen bool (MaybeT m a) (MaybeT m a)

-- ExceptT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGen bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  SymGen bool spec (ExceptT a m b)
  where
  genSymIndexed v = do
    x <- genSymIndexed @bool v
    return $ mrgFmap ExceptT x

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  SymGenSimple bool spec (ExceptT a m b)
  where
  genSymSimpleIndexed v = ExceptT <$> genSymSimpleIndexed @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  SymGenSimple bool (ExceptT e m a) (ExceptT e m a)
  where
  genSymSimpleIndexed (ExceptT v) = ExceptT <$> genSymSimpleIndexed @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    SymGenSimple bool () bool,
    SymGenSimple bool (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  SymGen bool (ExceptT e m a) (ExceptT e m a)
