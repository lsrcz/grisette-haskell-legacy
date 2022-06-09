{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Class.SimpleMergeable
  ( SimpleMergeable (..),
    SimpleMergeable1 (..),
    mrgIte1,
    SimpleMergeable2 (..),
    mrgIte2,
    UnionLike (..),
    mrgIf,
    merge,
    UnionPrjOp (..),
    pattern SingleU,
    pattern IfU,
  )
where

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
import Control.Monad.Trans.Cont
import qualified Control.Monad.RWS.Lazy as RWSLazy
import qualified Control.Monad.RWS.Strict as RWSStrict
import Data.Kind

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

instance (Generic a, Mergeable' bool (Rep a), SimpleMergeable' bool (Rep a)) => SimpleMergeable bool (Default a) where
  mrgIte cond (Default a) (Default b) = Default $ to $ mrgIte' cond (from a) (from b)

-- | Lifting of the 'SimpleMergeable' class to unary type constructors.
class SimpleMergeable1 bool u where
  -- | Lift 'mrgIte' through the type constructor.
  liftMrgIte :: (bool -> a -> a -> a) -> bool -> u a -> u a -> u a

-- | Lift the standard 'mrgIte' function through the type constructor.
mrgIte1 :: (SimpleMergeable1 bool u, SimpleMergeable bool a) => bool -> u a -> u a -> u a
mrgIte1 = liftMrgIte mrgIte

-- | Lifting of the 'SimpleMergeable' class to binary type constructors.
class (Mergeable2 bool u) => SimpleMergeable2 bool u where
  -- | Lift 'mrgIte' through the type constructor.
  liftMrgIte2 :: (bool -> a -> a -> a) -> (bool -> b -> b -> b) -> bool -> u a b -> u a b -> u a b

-- | Lift the standard 'mrgIte' function through the type constructor.
mrgIte2 :: (SimpleMergeable2 bool u, SimpleMergeable bool a, SimpleMergeable bool b) => bool -> u a b -> u a b -> u a b
mrgIte2 = liftMrgIte2 mrgIte mrgIte

-- | Special case of the 'Mergeable1' and 'SimpleMergeable1' class for type constructors
-- that are 'SimpleMergeable' when applied to any 'Mergeable' types.
--
-- Usually it is Union-like structures.
class (SimpleMergeable1 bool u, Mergeable1 bool u) => UnionLike bool u | u -> bool where
  -- | Wrap a single value in the union.
  single :: a -> u a

  -- | If-then-else on two union values.
  unionIf :: bool -> u a -> u a -> u a

  -- | Merge the contents with some merge strategy.
  --
  -- Be careful to call this directly in your code.
  -- The supplied merge strategy should be consistent with the type's root merge strategy,
  -- or some internal invariants would be broken and the program can crash.
  --
  -- This function is to be called when the 'Mergeable' constraint can not be resolved,
  -- e.g., the merge strategy for the contained type is given with 'Mergeable1'.
  -- In other cases, 'merge' is usually a better alternative.
  mergeWithStrategy :: MergeStrategy bool a -> u a -> u a

  -- | Symbolic @if@ control flow with the result merged with some merge strategy.
  --
  -- Be careful to call this directly in your code.
  -- The supplied merge strategy should be consistent with the type's root merge strategy,
  -- or some internal invariants would be broken and the program can crash.
  --
  -- This function to to be called when the 'Mergeable' constraint can not be resolved,
  -- e.g., the merge strategy for the contained type is given with 'Mergeable1'.
  -- In other cases, 'mrgIf' is usually a better alternative.
  mrgIfWithStrategy :: MergeStrategy bool a -> bool -> u a -> u a -> u a
  mrgIfWithStrategy s cond l r = mergeWithStrategy s $ unionIf cond l r
  
  mrgSingleWithStrategy :: MergeStrategy bool a -> a -> u a
  mrgSingleWithStrategy s = mergeWithStrategy s . single

-- | Symbolic @if@ control flow with the result merged with the type's root merge strategy.
--
-- | Equivalent to @mrgIfWithStrategy mergeStrategy@.
mrgIf :: (UnionLike bool u, Mergeable bool a) => bool -> u a -> u a -> u a
mrgIf = mrgIfWithStrategy mergeStrategy

-- | Merge the contents with the type's root merge strategy.
--
-- | Equivalent to @mergeWithStrategy mergeStrategy@.
merge :: (UnionLike bool u, Mergeable bool a) => u a -> u a
merge = mergeWithStrategy mergeStrategy

instance (SymBoolOp bool) => SimpleMergeable bool () where
  mrgIte _ t _ = t

instance (SymBoolOp bool, SimpleMergeable bool a, SimpleMergeable bool b) => SimpleMergeable bool (a, b) where
  mrgIte cond (a1, b1) (a2, b2) = (mrgIte cond a1 a2, mrgIte cond b1 b2)

instance (SymBoolOp bool, SimpleMergeable bool a) => SimpleMergeable1 bool ((,) a) where
  liftMrgIte mb cond (a1, b1) (a2, b2) = (mrgIte cond a1 a2, mb cond b1 b2)

instance (SymBoolOp bool) => SimpleMergeable2 bool (,) where
  liftMrgIte2 ma mb cond (a1, b1) (a2, b2) = (ma cond a1 a2, mb cond b1 b2)

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
  mrgIte = mrgIte1

instance (SymBoolOp bool) => SimpleMergeable1 bool ((->) a) where
  liftMrgIte ms cond t f = \v -> ms cond (t v) (f v)

instance (SymBoolOp bool, UnionLike bool m, Mergeable bool a) => SimpleMergeable bool (MaybeT m a) where
  mrgIte = mrgIf

instance (SymBoolOp bool, UnionLike bool m) => SimpleMergeable1 bool (MaybeT m) where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance (SymBoolOp bool, UnionLike bool m) => UnionLike bool (MaybeT m) where
  mergeWithStrategy s (MaybeT v) = MaybeT $ mergeWithStrategy (liftMergeStrategy s) v
  mrgIfWithStrategy s cond (MaybeT t) (MaybeT f) = MaybeT $ mrgIfWithStrategy (liftMergeStrategy s) cond t f
  single = MaybeT . single . return
  unionIf cond (MaybeT l) (MaybeT r) = MaybeT $ unionIf cond l r

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e, Mergeable bool a) =>
  SimpleMergeable bool (ExceptT e m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e) =>
  SimpleMergeable1 bool (ExceptT e m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool e) =>
  UnionLike bool (ExceptT e m)
  where
  mergeWithStrategy s (ExceptT v) = ExceptT $ mergeWithStrategy (liftMergeStrategy s) v
  mrgIfWithStrategy s cond (ExceptT t) (ExceptT f) = ExceptT $ mrgIfWithStrategy (liftMergeStrategy s) cond t f
  single = ExceptT . single . return
  unionIf cond (ExceptT l) (ExceptT r) = ExceptT $ unionIf cond l r

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionLike bool m) =>
  SimpleMergeable bool (StateLazy.StateT s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m) =>
  SimpleMergeable1 bool (StateLazy.StateT s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m) =>
  UnionLike bool (StateLazy.StateT s m)
  where
  mergeWithStrategy ms (StateLazy.StateT f) =
    StateLazy.StateT $ \v -> mergeWithStrategy (liftMergeStrategy2 ms mergeStrategy) $ f v
  mrgIfWithStrategy s cond (StateLazy.StateT t) (StateLazy.StateT f) =
    StateLazy.StateT $ \v -> mrgIfWithStrategy (liftMergeStrategy2 s mergeStrategy) cond (t v) (f v)
  single x = StateLazy.StateT $ \s -> single (x, s)
  unionIf cond (StateLazy.StateT l) (StateLazy.StateT r) =
    StateLazy.StateT $ \s -> unionIf cond (l s) (r s)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionLike bool m) =>
  SimpleMergeable bool (StateStrict.StateT s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m) =>
  SimpleMergeable1 bool (StateStrict.StateT s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m) =>
  UnionLike bool (StateStrict.StateT s m)
  where
  mergeWithStrategy ms (StateStrict.StateT f) =
    StateStrict.StateT $ \v -> mergeWithStrategy (liftMergeStrategy2 ms mergeStrategy) $ f v
  mrgIfWithStrategy s cond (StateStrict.StateT t) (StateStrict.StateT f) =
    StateStrict.StateT $ \v -> mrgIfWithStrategy (liftMergeStrategy2 s mergeStrategy) cond (t v) (f v)
  single x = StateStrict.StateT $ \s -> single (x, s)
  unionIf cond (StateStrict.StateT l) (StateStrict.StateT r) =
    StateStrict.StateT $ \s -> unionIf cond (l s) (r s)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionLike bool m, Monoid s) =>
  SimpleMergeable bool (WriterLazy.WriterT s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m, Monoid s) =>
  SimpleMergeable1 bool (WriterLazy.WriterT s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m, Monoid s) =>
  UnionLike bool (WriterLazy.WriterT s m)
  where
  mergeWithStrategy ms (WriterLazy.WriterT f) = WriterLazy.WriterT $ mergeWithStrategy (liftMergeStrategy2 ms mergeStrategy) f
  mrgIfWithStrategy s cond (WriterLazy.WriterT t) (WriterLazy.WriterT f) =
    WriterLazy.WriterT $ mrgIfWithStrategy (liftMergeStrategy2 s mergeStrategy) cond t f
  single x = WriterLazy.WriterT $ single (x, mempty)
  unionIf cond (WriterLazy.WriterT l) (WriterLazy.WriterT r) =
    WriterLazy.WriterT $ unionIf cond l r

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionLike bool m, Monoid s) =>
  SimpleMergeable bool (WriterStrict.WriterT s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m, Monoid s) =>
  SimpleMergeable1 bool (WriterStrict.WriterT s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionLike bool m, Monoid s) =>
  UnionLike bool (WriterStrict.WriterT s m)
  where
  mergeWithStrategy ms (WriterStrict.WriterT f) = WriterStrict.WriterT $ mergeWithStrategy (liftMergeStrategy2 ms mergeStrategy) f
  mrgIfWithStrategy s cond (WriterStrict.WriterT t) (WriterStrict.WriterT f) =
    WriterStrict.WriterT $ mrgIfWithStrategy (liftMergeStrategy2 s mergeStrategy) cond t f
  single x = WriterStrict.WriterT $ single (x, mempty)
  unionIf cond (WriterStrict.WriterT l) (WriterStrict.WriterT r) =
    WriterStrict.WriterT $ unionIf cond l r

instance
  (SymBoolOp bool, Mergeable bool a, UnionLike bool m) =>
  SimpleMergeable bool (ReaderT s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable1 bool (ReaderT s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  UnionLike bool (ReaderT s m)
  where
  mergeWithStrategy ms (ReaderT f) = ReaderT $ \v -> mergeWithStrategy ms $ f v
  mrgIfWithStrategy s cond (ReaderT t) (ReaderT f) =
    ReaderT $ \v -> mrgIfWithStrategy s cond (t v) (f v)
  single x = ReaderT $ \_ -> single x
  unionIf cond (ReaderT l) (ReaderT r) = ReaderT $ \s -> unionIf cond (l s) (r s)

instance (SymBoolOp bool, SimpleMergeable bool a) => SimpleMergeable bool (Identity a) where
  mrgIte cond (Identity l) (Identity r) = Identity $ mrgIte cond l r

instance (SymBoolOp bool) => SimpleMergeable1 bool Identity where
  liftMrgIte mite cond (Identity l) (Identity r) = Identity $ mite cond l r

instance (SymBoolOp bool, UnionLike bool m, Mergeable bool a) => SimpleMergeable bool (IdentityT m a) where
  mrgIte = mrgIf

instance (SymBoolOp bool, UnionLike bool m) => SimpleMergeable1 bool (IdentityT m) where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance (SymBoolOp bool, UnionLike bool m) => UnionLike bool (IdentityT m) where
  mergeWithStrategy ms (IdentityT f) =
    IdentityT $ mergeWithStrategy ms f
  mrgIfWithStrategy s cond (IdentityT l) (IdentityT r) = IdentityT $ mrgIfWithStrategy s cond l r
  single x = IdentityT $ single x
  unionIf cond (IdentityT l) (IdentityT r) = IdentityT $ unionIf cond l r

instance (SymBoolOp bool, UnionLike bool m, Mergeable bool r) => SimpleMergeable bool (ContT r m a) where
  mrgIte cond (ContT l) (ContT r) = ContT $ \c -> mrgIf cond (l c) (r c)

instance (SymBoolOp bool, UnionLike bool m, Mergeable bool r) => SimpleMergeable1 bool (ContT r m) where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance (SymBoolOp bool, UnionLike bool m, Mergeable bool r) => UnionLike bool (ContT r m) where
  mergeWithStrategy _ (ContT f) = ContT $ \c -> merge (f c)
  mrgIfWithStrategy _ cond (ContT l) (ContT r) = ContT $ \c -> mrgIf cond (l c) (r c)
  single x = ContT $ \c -> c x
  unionIf cond (ContT l) (ContT r) = ContT $ \c -> unionIf cond (l c) (r c)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool w, Monoid w, Mergeable bool a, UnionLike bool m) =>
  SimpleMergeable bool (RWSLazy.RWST r w s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool w, Monoid w, UnionLike bool m) =>
  SimpleMergeable1 bool (RWSLazy.RWST r w s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool w, Monoid w, UnionLike bool m) =>
  UnionLike bool (RWSLazy.RWST r w s m)
  where
  mergeWithStrategy ms (RWSLazy.RWST f) =
    RWSLazy.RWST $ \r s -> mergeWithStrategy (liftMergeStrategy3 ms mergeStrategy mergeStrategy) $ f r s
  mrgIfWithStrategy ms cond (RWSLazy.RWST t) (RWSLazy.RWST f) =
    RWSLazy.RWST $ \r s -> mrgIfWithStrategy (liftMergeStrategy3 ms mergeStrategy mergeStrategy) cond (t r s) (f r s)
  single x = RWSLazy.RWST $ \_ s -> single (x, s, mempty)
  unionIf cond (RWSLazy.RWST t) (RWSLazy.RWST f) =
    RWSLazy.RWST $ \r s -> unionIf cond (t r s) (f r s)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool w, Monoid w, Mergeable bool a, UnionLike bool m) =>
  SimpleMergeable bool (RWSStrict.RWST r w s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool w, Monoid w, UnionLike bool m) =>
  SimpleMergeable1 bool (RWSStrict.RWST r w s m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool w, Monoid w, UnionLike bool m) =>
  UnionLike bool (RWSStrict.RWST r w s m)
  where
  mergeWithStrategy ms (RWSStrict.RWST f) =
    RWSStrict.RWST $ \r s -> mergeWithStrategy (liftMergeStrategy3 ms mergeStrategy mergeStrategy) $ f r s
  mrgIfWithStrategy ms cond (RWSStrict.RWST t) (RWSStrict.RWST f) =
    RWSStrict.RWST $ \r s -> mrgIfWithStrategy (liftMergeStrategy3 ms mergeStrategy mergeStrategy) cond (t r s) (f r s)
  single x = RWSStrict.RWST $ \_ s -> single (x, s, mempty)
  unionIf cond (RWSStrict.RWST t) (RWSStrict.RWST f) =
    RWSStrict.RWST $ \r s -> unionIf cond (t r s) (f r s)

class (UnionLike bool u) => UnionPrjOp bool (u :: Type -> Type) | u -> bool where
  -- | Pattern match to extract single values.
  singleView :: u a -> Maybe a

  -- | Pattern match to extract guard values.
  ifView :: u a -> Maybe (bool, u a, u a)

  -- | The leftmost value in the union.
  leftMost :: u a -> a

-- | Pattern match to extract single values with 'singleView'.
pattern SingleU :: UnionPrjOp bool u => a -> u a
pattern SingleU x <-
  (singleView -> Just x)
  where
    SingleU x = single x

-- | Pattern match to extract guard values with 'guardView'
pattern IfU :: UnionPrjOp bool u => bool -> u a -> u a -> u a
pattern IfU c t f <-
  (ifView -> Just (c, t, f))
  where
    IfU c t f = unionIf c t f
