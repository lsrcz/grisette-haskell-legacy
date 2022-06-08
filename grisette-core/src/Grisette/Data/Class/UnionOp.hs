{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Class.UnionOp
  ( UnionOp (..),
    UnionPrjOp (..),
    pattern SingleU,
    pattern GuardU,
  )
where

import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Lazy as StateLazy
import qualified Control.Monad.Trans.State.Strict as StateStrict
import qualified Control.Monad.Trans.Writer.Lazy as WriterLazy
import qualified Control.Monad.Trans.Writer.Strict as WriterStrict
import Data.Kind
import Grisette.Data.Class.Bool
import Control.Monad.Trans.Cont
import qualified Control.Monad.Trans.RWS.Lazy as RWSLazy
import qualified Control.Monad.Trans.RWS.Strict as RWSStrict

-- | Basic operations for union-like containers.
-- These operations does not ensure the result to be merged.
class (SymBoolOp bool) => UnionOp bool (u :: Type -> Type) | u -> bool where
  -- | Wrap a single value in the union.
  single :: a -> u a

  -- | If-then-else on two union values.
  guard :: bool -> u a -> u a -> u a

class (UnionOp bool u) => UnionPrjOp bool (u :: Type -> Type) | u -> bool where
  -- | Pattern match to extract single values.
  singleView :: u a -> Maybe a

  -- | Pattern match to extract guard values.
  guardView :: u a -> Maybe (bool, u a, u a)

  -- | The leftmost value in the union.
  leftMost :: u a -> a

-- | Pattern match to extract single values with 'singleView'.
pattern SingleU :: UnionPrjOp bool u => a -> u a
pattern SingleU x <-
  (singleView -> Just x)
  where
    SingleU x = single x

-- | Pattern match to extract guard values with 'guardView'
pattern GuardU :: UnionPrjOp bool u => bool -> u a -> u a -> u a
pattern GuardU c t f <-
  (guardView -> Just (c, t, f))
  where
    GuardU c t f = guard c t f

instance (SymBoolOp bool, UnionOp bool m) => UnionOp bool (MaybeT m) where
  single = MaybeT . single . return
  guard cond (MaybeT l) (MaybeT r) = MaybeT $ guard cond l r

instance (SymBoolOp bool, UnionOp bool m) => UnionOp bool (ExceptT e m) where
  single = ExceptT . single . return
  guard cond (ExceptT l) (ExceptT r) = ExceptT $ guard cond l r

instance
  (SymBoolOp bool, UnionOp bool m) =>
  UnionOp bool (StateLazy.StateT s m)
  where
  single x = StateLazy.StateT $ \s -> single (x, s)
  guard cond (StateLazy.StateT l) (StateLazy.StateT r) =
    StateLazy.StateT $ \s -> guard cond (l s) (r s)

instance
  (SymBoolOp bool, UnionOp bool m) =>
  UnionOp bool (StateStrict.StateT s m)
  where
  single x = StateStrict.StateT $ \s -> single (x, s)
  guard cond (StateStrict.StateT l) (StateStrict.StateT r) =
    StateStrict.StateT $ \s -> guard cond (l s) (r s)

instance
  (SymBoolOp bool, UnionOp bool m, Monoid w) =>
  UnionOp bool (WriterLazy.WriterT w m)
  where
  single x = WriterLazy.WriterT $ single (x, mempty)
  guard cond (WriterLazy.WriterT l) (WriterLazy.WriterT r) =
    WriterLazy.WriterT $ guard cond l r

instance
  (SymBoolOp bool, UnionOp bool m, Monoid w) =>
  UnionOp bool (WriterStrict.WriterT w m)
  where
  single x = WriterStrict.WriterT $ single (x, mempty)
  guard cond (WriterStrict.WriterT l) (WriterStrict.WriterT r) =
    WriterStrict.WriterT $ guard cond l r

instance
  (SymBoolOp bool, UnionOp bool m) =>
  UnionOp bool (ReaderT s m)
  where
  single x = ReaderT $ \_ -> single x
  guard cond (ReaderT l) (ReaderT r) = ReaderT $ \s -> guard cond (l s) (r s)

instance
  (SymBoolOp bool, UnionOp bool m) =>
  UnionOp bool (IdentityT m)
  where
  single x = IdentityT $ single x
  guard cond (IdentityT l) (IdentityT r) = IdentityT $ guard cond l r

instance (SymBoolOp bool, UnionOp bool m) => UnionOp bool (ContT r m) where
  single x = ContT $ \c -> c x
  guard cond (ContT l) (ContT r) = ContT $ \c -> guard cond (l c) (r c)

instance
  (SymBoolOp bool, Monoid w, UnionOp bool m) =>
  UnionOp bool (RWSLazy.RWST r w s m)
  where
    single x = RWSLazy.RWST $ \_ s -> single (x, s, mempty)
    guard cond (RWSLazy.RWST t) (RWSLazy.RWST f) =
      RWSLazy.RWST $ \r s -> guard cond (t r s) (f r s)

instance
  (SymBoolOp bool, Monoid w, UnionOp bool m) =>
  UnionOp bool (RWSStrict.RWST r w s m)
  where
    single x = RWSStrict.RWST $ \_ s -> single (x, s, mempty)
    guard cond (RWSStrict.RWST t) (RWSStrict.RWST f) =
      RWSStrict.RWST $ \r s -> guard cond (t r s) (f r s)

