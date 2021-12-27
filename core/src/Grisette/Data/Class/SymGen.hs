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
  ( SymGen (..),
    genSym,
    SymGenSimple (..),
    genSymSimple,
    SymGenNoSpec (..),
    SymGenSimpleNoSpec (..),
    genSymIndexedWithDerivedNoSpec,
    genSymSimpleIndexedWithDerivedNoSpec,
    genSymIndexedWithDerivedSameShape,
  )
where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Generics.Deriving
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Grisette.Data.Functor

class (SymBoolOp bool, Mergeable bool a) => SymGen bool spec a where
  genSymIndexed :: spec -> State (Int, String) (UnionMBase bool a)

genSym :: (SymGen bool spec a) => spec -> String -> UnionMBase bool a
genSym spec name = evalState (genSymIndexed spec) (0, name)

class SymGen bool spec a => SymGenSimple bool spec a where
  genSymSimpleIndexed :: spec -> State (Int, String) a

genSymSimple :: forall bool spec a. (SymGenSimple bool spec a) => spec -> String -> a
genSymSimple spec name = evalState (genSymSimpleIndexed @bool spec) (0, name)

class SymGenNoSpec bool a where
  genSymIndexedNoSpec :: State (Int, String) (UnionMBase bool (a c))

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
  forall bool a.
  (Generic a, SymBoolOp bool, SymGenNoSpec bool (Rep a), Mergeable bool a) =>
  State (Int, String) (UnionMBase bool a)
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
  genSymSimpleIndexedNoSpec :: State (Int, String) (a c)

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
  forall bool a.
  (Generic a, SymBoolOp bool, SymGenSimpleNoSpec bool (Rep a)) =>
  State (Int, String) a
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
  genSymSameShapeIndexed :: a c -> State (Int, String) (a c)

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
  forall bool a.
  (Generic a, SymGenSameShape bool (Rep a)) =>
  a ->
  State (Int, String) a
genSymIndexedWithDerivedSameShape a = to <$> genSymSameShapeIndexed @bool @(Rep a) (from a)

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
  (SymBoolOp bool, SymGenSimple bool () bool, SymGenSimple bool a a, Mergeable bool a) =>
  SymGenSimple bool [a] [a]
  where
  genSymSimpleIndexed v = genSymIndexedWithDerivedSameShape @bool v

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
