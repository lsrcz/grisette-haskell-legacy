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
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import GHC.Generics
import Generics.Deriving
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.Utils.CConst

-- | Auxiliary class for the generic derivation for the 'SimpleMergeable' class.
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

-- | This class indicates that a type has a simple root merge strategy.
class Mergeable bool a => SimpleMergeable bool a where
  -- | Performs if-then-else with the simple root merge strategy.
  mrgIte :: bool -> a -> a -> a

instance (Generic a, Mergeable bool (Default a), SimpleMergeable' bool (Rep a)) => SimpleMergeable bool (Default a) where
  mrgIte cond (Default a) (Default b) = Default $ to $ mrgIte' cond (from a) (from b)

-- | Lifting of the 'SimpleMergeable' class to unary type constructors.
class (Mergeable1 bool u) => SimpleMergeable1 bool u where
  -- | Resolves the 'SimpleMergeable' constraint through the type constructor.
  --
  -- Usually you will not need to write this function manually.
  -- It should be available after you implement the 'SimpleMergeable' class.
  withSimpleMergeableT :: forall a t. (SimpleMergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withSimpleMergeableT ::
    (forall b. SimpleMergeable bool b => SimpleMergeable bool (u b)) =>
    forall a t.
    (SimpleMergeable bool a) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withSimpleMergeableT v = v

  -- | Perform 'mrgIte' through the type constructor.
  --
  -- Usually you will not need to write this function manually.
  -- It should be available after you implement the 'SimpleMergeable' class.
  mrgIte1 :: (SimpleMergeable bool a) => bool -> u a -> u a -> u a
  default mrgIte1 ::
    (forall b. SimpleMergeable bool b => SimpleMergeable bool (u b)) =>
    (SimpleMergeable bool a) =>
    bool ->
    u a ->
    u a ->
    u a
  mrgIte1 cond t f = mrgIte cond t f

-- | Special case of the 'SimpleMergeable1' class where 'SimpleMergeable'
-- is available through the type constructor even if the type constructor is
-- applied to a 'Mergeable' type rather than a 'SimpleMergeable' type.
class (SimpleMergeable1 bool u) => UnionSimpleMergeable1 bool u where
  -- | Resolves the 'SimpleMergeable' constraint through the type constructor.
  --
  -- Usually you will not need to write this function manually.
  -- It should be available after you implement the 'SimpleMergeable' class.
  withUnionSimpleMergeableT :: forall a t. (Mergeable bool a) => (SimpleMergeable bool (u a) => t a) -> t a
  default withUnionSimpleMergeableT ::
    (forall b. Mergeable bool b => SimpleMergeable bool (u b)) =>
    forall a t.
    (Mergeable bool a) =>
    (SimpleMergeable bool (u a) => t a) ->
    t a
  withUnionSimpleMergeableT v = v

  -- | Perform 'mrgIte' through the type constructor.
  --
  -- Usually you will not need to write this function manually.
  -- It should be available after you implement the 'SimpleMergeable' class.
  mrgIteu1 :: (Mergeable bool a) => bool -> u a -> u a -> u a
  default mrgIteu1 ::
    (forall b. Mergeable bool b => SimpleMergeable bool (u b)) =>
    (Mergeable bool a) =>
    bool ->
    u a ->
    u a ->
    u a
  mrgIteu1 cond t f = mrgIte cond t f

-- | Resolves the 'SimpleMergeable' constraint through a 'SimpleMergeable1' type constructor.
withSimpleMergeable :: forall bool u a b. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withSimpleMergeable v = unCConst $ withSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

-- | Resolves the 'SimpleMergeable' constraint through a 'SimpleMergeable1' type constructor.
withSimpleMergeableU :: forall bool u a. (SimpleMergeable1 bool u, SimpleMergeable bool a) => (SimpleMergeable bool (u a) => u a) -> u a
withSimpleMergeableU = withSimpleMergeable @bool @u @a

-- | Resolves the 'SimpleMergeable' constraint through a 'UnionSimpleMergeable1' type constructor.
withUnionSimpleMergeable :: forall bool u a b. (UnionSimpleMergeable1 bool u, Mergeable bool a) => (SimpleMergeable bool (u a) => b) -> b
withUnionSimpleMergeable v = unCConst $ withUnionSimpleMergeableT @bool @u @a @(CConst (SimpleMergeable bool (u a)) b) $ CConst v

-- | Resolves the 'SimpleMergeable' constraint through a 'UnionSimpleMergeable1' type constructor.
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

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable bool (WriterLazy.WriterT s m a)
  where
  mrgIte cond (WriterLazy.WriterT t) (WriterLazy.WriterT f) =
    withUnionSimpleMergeable @bool @m @(a, s) $
      WriterLazy.WriterT $ mrgIte cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (WriterLazy.WriterT s m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (WriterLazy.WriterT s m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable bool (WriterStrict.WriterT s m a)
  where
  mrgIte cond (WriterStrict.WriterT t) (WriterStrict.WriterT f) =
    withUnionSimpleMergeable @bool @m @(a, s) $
      WriterStrict.WriterT $ mrgIte cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (WriterStrict.WriterT s m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (WriterStrict.WriterT s m)

instance
  (SymBoolOp bool, Mergeable bool a, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable bool (ReaderT s m a)
  where
  mrgIte cond (ReaderT t) (ReaderT f) =
    withUnionSimpleMergeable @bool @m @a $
      ReaderT $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (ReaderT s m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (ReaderT s m)

instance (SymBoolOp bool, SimpleMergeable bool a) => SimpleMergeable bool (Identity a) where
  mrgIte cond (Identity l) (Identity r) = Identity $ mrgIte cond l r

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool a) => SimpleMergeable bool (IdentityT m a) where
  mrgIte cond (IdentityT l) (IdentityT r) = IdentityT $ mrgIteu1 cond l r

instance (SymBoolOp bool) => SimpleMergeable1 bool Identity where
  mrgIte1 cond (Identity l) (Identity r) = Identity $ mrgIte cond l r

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m) => SimpleMergeable1 bool (IdentityT m) where
  mrgIte1 cond (IdentityT l) (IdentityT r) = IdentityT $ mrgIteu1 cond l r

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m) => UnionSimpleMergeable1 bool (IdentityT m) where
  mrgIteu1 cond (IdentityT l) (IdentityT r) = IdentityT $ mrgIteu1 cond l r
