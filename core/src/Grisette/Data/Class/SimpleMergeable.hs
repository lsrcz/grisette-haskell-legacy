{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.SimpleMergeable
  ( SimpleMergeable (..),
    SimpleMergeable1 (..),
    UnionSimpleMergeable1 (..),
    withSimpleMergeable,
    withUnionSimpleMergeable,
    withSimpleMergeableU,
    withUnionSimpleMergeableU,
  )
where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Except
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe
import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.Utils.CConst
import Generics.Deriving

class SimpleMergeable' bool f where
  mrgIte' :: bool -> f a -> f a -> f a

instance (SimpleMergeable' bool U1) where
  mrgIte' = \_ t _ -> t

instance (SimpleMergeable' bool V1) where
  mrgIte' = \_ t _ -> t

instance (SimpleMergeable bool c) => (SimpleMergeable' bool (K1 i c)) where
  mrgIte' = \cond (K1 a) (K1 b) -> K1 $ mrgIte cond a b

instance (SimpleMergeable' bool a) => (SimpleMergeable' bool (M1 i c a)) where
  mrgIte' = \cond (M1 a) (M1 b) -> M1 $ mrgIte' cond a b

instance (SimpleMergeable' bool a, SimpleMergeable' bool b) => (SimpleMergeable' bool (a :*: b)) where
  mrgIte' = \cond (a1 :*: a2) (b1 :*: b2) -> mrgIte' cond a1 b1 :*: mrgIte' cond a2 b2

class Mergeable bool a => SimpleMergeable bool a where
  mrgIte :: bool -> a -> a -> a

instance (Generic a, Mergeable bool (Default a), SimpleMergeable' bool (Rep a)) => SimpleMergeable bool (Default a) where
  mrgIte cond (Default a) (Default b) = Default $ to $ mrgIte' cond (from a) (from b)

class (Mergeable1 bool u) => SimpleMergeable1 bool u where
  withSimpleMergeableT :: forall a t. (SimpleMergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withSimpleMergeableT ::
    (forall b. SimpleMergeable bool b => SimpleMergeable bool (u b)) =>
    forall a t.
    (SimpleMergeable bool a) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withSimpleMergeableT v = v
  mrgIte1 :: (SimpleMergeable bool a) => bool -> u a -> u a -> u a
  default mrgIte1 ::
    (forall b. SimpleMergeable bool b => SimpleMergeable bool (u b)) =>
    (SimpleMergeable bool a) =>
    bool ->
    u a ->
    u a ->
    u a
  mrgIte1 cond t f = mrgIte cond t f

class (SimpleMergeable1 bool u) => UnionSimpleMergeable1 bool u where
  withUnionSimpleMergeableT :: forall a t. (Mergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withUnionSimpleMergeableT ::
    (forall b. Mergeable bool b => SimpleMergeable bool (u b)) =>
    forall a t.
    (Mergeable bool a) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withUnionSimpleMergeableT v = v
  mrgIteu1 :: (Mergeable bool a) => bool -> u a -> u a -> u a
  default mrgIteu1 ::
    (forall b. Mergeable bool b => SimpleMergeable bool (u b)) =>
    (Mergeable bool a) =>
    bool ->
    u a ->
    u a ->
    u a
  mrgIteu1 cond t f = mrgIte cond t f

withSimpleMergeable :: forall bool u a b. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withSimpleMergeable v = unCConst $ withSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

withSimpleMergeableU :: forall bool u a. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withSimpleMergeableU = withSimpleMergeable @bool @u @a

withUnionSimpleMergeable :: forall bool u a b. (UnionSimpleMergeable1 bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withUnionSimpleMergeable v = unCConst $ withUnionSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

withUnionSimpleMergeableU :: forall bool u a. (UnionSimpleMergeable1 bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withUnionSimpleMergeableU = withUnionSimpleMergeable @bool @u @a

instance (SymBoolOp bool) => SimpleMergeable bool () where
  mrgIte _ t _ = t

instance (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b) => SimpleMergeable bool (a, b) where
  mrgIte cond (a1, b1) (a2, b2) = (mrgIte cond a1 a2, mrgIte cond b1 b2)

instance
  (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b, SimpleMergeable bool c) =>
  SimpleMergeable bool (a, b, c)
  where
  mrgIte cond (a1, b1, c1) (a2, b2, c2) = (mrgIte cond a1 a2, mrgIte cond b1 b2, mrgIte cond c1 c2)

instance
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    SimpleMergeable bool b,
    SimpleMergeable bool c,
    SimpleMergeable bool d
  ) =>
  SimpleMergeable bool (a, b, c, d)
  where
  mrgIte cond (a1, b1, c1, d1) (a2, b2, c2, d2) =
    (mrgIte cond a1 a2, mrgIte cond b1 b2, mrgIte cond c1 c2, mrgIte cond d1 d2)

instance
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    SimpleMergeable bool b,
    SimpleMergeable bool c,
    SimpleMergeable bool d,
    SimpleMergeable bool e
  ) =>
  SimpleMergeable bool (a, b, c, d, e)
  where
  mrgIte cond (a1, b1, c1, d1, e1) (a2, b2, c2, d2, e2) =
    (mrgIte cond a1 a2, mrgIte cond b1 b2, mrgIte cond c1 c2, mrgIte cond d1 d2, mrgIte cond e1 e2)

instance
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    SimpleMergeable bool b,
    SimpleMergeable bool c,
    SimpleMergeable bool d,
    SimpleMergeable bool e,
    SimpleMergeable bool f
  ) =>
  SimpleMergeable bool (a, b, c, d, e, f)
  where
  mrgIte cond (a1, b1, c1, d1, e1, f1) (a2, b2, c2, d2, e2, f2) =
    (mrgIte cond a1 a2, mrgIte cond b1 b2, mrgIte cond c1 c2, mrgIte cond d1 d2, mrgIte cond e1 e2, mrgIte cond f1 f2)

instance
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    SimpleMergeable bool b,
    SimpleMergeable bool c,
    SimpleMergeable bool d,
    SimpleMergeable bool e,
    SimpleMergeable bool f,
    SimpleMergeable bool g
  ) =>
  SimpleMergeable bool (a, b, c, d, e, f, g)
  where
  mrgIte cond (a1, b1, c1, d1, e1, f1, g1) (a2, b2, c2, d2, e2, f2, g2) =
    ( mrgIte cond a1 a2,
      mrgIte cond b1 b2,
      mrgIte cond c1 c2,
      mrgIte cond d1 d2,
      mrgIte cond e1 e2,
      mrgIte cond f1 f2,
      mrgIte cond g1 g2
    )

instance
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    SimpleMergeable bool b,
    SimpleMergeable bool c,
    SimpleMergeable bool d,
    SimpleMergeable bool e,
    SimpleMergeable bool f,
    SimpleMergeable bool g,
    SimpleMergeable bool h
  ) =>
  SimpleMergeable bool (a, b, c, d, e, f, g, h)
  where
  mrgIte cond (a1, b1, c1, d1, e1, f1, g1, h1) (a2, b2, c2, d2, e2, f2, g2, h2) =
    ( mrgIte cond a1 a2,
      mrgIte cond b1 b2,
      mrgIte cond c1 c2,
      mrgIte cond d1 d2,
      mrgIte cond e1 e2,
      mrgIte cond f1 f2,
      mrgIte cond g1 g2,
      mrgIte cond h1 h2
    )

instance (SymBoolOp bool, SimpleMergeable bool b) => SimpleMergeable bool (a -> b) where
  mrgIte cond t f = \v -> mrgIte cond (t v) (f v)

instance (SymBoolOp bool) => SimpleMergeable1 bool ((->) a)

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool a) => SimpleMergeable bool (MaybeT m a) where
  mrgIte cond (MaybeT t) (MaybeT f) = MaybeT $ mrgIteu1 cond t f

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m) => SimpleMergeable1 bool (MaybeT m)

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m) => UnionSimpleMergeable1 bool (MaybeT m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ExceptT e m a)
  where
  mrgIte cond (ExceptT t) (ExceptT f) =
    withUnionSimpleMergeable @bool @m @(Either e a) $ ExceptT $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ExceptT e m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool e, Functor m) =>
  UnionSimpleMergeable1 bool (ExceptT e m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  SimpleMergeable bool (Coroutine sus m a)
  where
  mrgIte cond (Coroutine t) (Coroutine f) =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withUnionSimpleMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        Coroutine $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable1 bool sus) =>
  SimpleMergeable1 bool (Coroutine sus m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable1 bool sus) =>
  UnionSimpleMergeable1 bool (Coroutine sus m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable bool (StateLazy.StateT s m a)
  where
  mrgIte cond (StateLazy.StateT t) (StateLazy.StateT f) =
    withUnionSimpleMergeable @bool @m @(a, s) $
      withSimpleMergeable @bool @((->) s) @(m (a, s)) $
        StateLazy.StateT $ mrgIte cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (StateLazy.StateT s m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (StateLazy.StateT s m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable bool (StateStrict.StateT s m a)
  where
  mrgIte cond (StateStrict.StateT t) (StateStrict.StateT f) =
    withUnionSimpleMergeable @bool @m @(a, s) $
      withSimpleMergeable @bool @((->) s) @(m (a, s)) $
        StateStrict.StateT $ mrgIte cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (StateStrict.StateT s m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (StateStrict.StateT s m)
