{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Instances where

import Control.Carrier.Error.Either
import Control.Carrier.Lift
import Control.Carrier.State.Strict
import qualified Control.Carrier.Error.Church as EC
import Grisette

instance (SymBoolOp bool, UnionMergeable1 bool m) =>
  Mergeable bool (EC.ErrorC e m a) where
    mergeStrategy = SimpleStrategy $ \cond (EC.ErrorC l) (EC.ErrorC r) ->
      EC.ErrorC $ \ef af -> guard cond (l ef af) (r ef af)

instance (SymBoolOp bool, UnionMergeable1 bool m) =>
  Mergeable1 bool (EC.ErrorC e m) where
    liftMergeStrategy _ = SimpleStrategy $ \cond (EC.ErrorC l) (EC.ErrorC r) ->
      EC.ErrorC $ \ef af -> guard cond (l ef af) (r ef af)

instance (SymBoolOp bool, UnionMergeable1 bool m) =>
  SimpleMergeable bool (EC.ErrorC e m a) where
  mrgIte bool (EC.ErrorC l) (EC.ErrorC r) = EC.ErrorC $ \ef af ->
    guard bool (l ef af) (r ef af)

instance (SymBoolOp bool, UnionMergeable1 bool m) =>
  SimpleMergeable1 bool (EC.ErrorC e m) where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance (SymBoolOp bool, UnionMergeable1 bool m) =>
  UnionOp bool (EC.ErrorC e m) where
    single a = EC.ErrorC $ \_ leaf -> leaf a
    guard cond (EC.ErrorC l) (EC.ErrorC r) =
      EC.ErrorC $ \ef af -> guard cond (l ef af) (r ef af)

instance (SymBoolOp bool, UnionMergeable1 bool m) =>
  UnionMergeable1 bool (EC.ErrorC e m) where
    mergeWithStrategy _ = id
    mrgIfWithStrategy _ cond (EC.ErrorC l) (EC.ErrorC r) = EC.ErrorC $
      \ef af -> guard cond (l ef af) (r ef af)

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ErrorC e m a)
  where
  mergeStrategy = wrapMergeStrategy mergeStrategy ErrorC (\(ErrorC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ErrorC e m) where
  liftMergeStrategy ms = wrapMergeStrategy (liftMergeStrategy ms) ErrorC (\(ErrorC et) -> et)

instance
  (SymBoolOp bool, UnionMergeable1 bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ErrorC e m a)
  where
  mrgIte cond (ErrorC t) (ErrorC f) = ErrorC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionMergeable1 bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ErrorC e m)
  where
  liftMrgIte s = mrgIfWithStrategy (SimpleStrategy s)

instance
  (SymBoolOp bool, UnionOp bool m, Mergeable bool e, Functor m) =>
  UnionOp bool (ErrorC e m)
  where
  single a = ErrorC $ single a
  guard cond (ErrorC t) (ErrorC f) = ErrorC $ guard cond t f

instance
  (SymBoolOp bool, UnionMergeable1 bool m, Mergeable bool e, Functor m) =>
  UnionMergeable1 bool (ErrorC e m)
  where
  mergeWithStrategy s (ErrorC et) = ErrorC $ mergeWithStrategy s et
  mrgIfWithStrategy s cond (ErrorC l) (ErrorC r) = ErrorC $ mrgIfWithStrategy s cond l r

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateC s m a)
  where
  mergeStrategy = wrapMergeStrategy (liftMergeStrategy mergeStrategy1) StateC (\(StateC f) -> f)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) =>
  Mergeable1 bool (StateC s m)
  where
  liftMergeStrategy s = wrapMergeStrategy (liftMergeStrategy (liftMergeStrategy (liftMergeStrategy s))) StateC (\(StateC f) -> f)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionMergeable1 bool m) =>
  SimpleMergeable bool (StateC s m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, Mergeable bool s, UnionMergeable1 bool m) =>
  SimpleMergeable1 bool (StateC s m)
  where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy

instance
  (SymBoolOp bool, Mergeable bool s, UnionOp bool m) =>
  UnionOp bool (StateC s m)
  where
    single a = StateC $ \s -> single (s, a)
    guard cond (StateC l) (StateC r) = StateC $ \s -> guard cond (l s) (r s)

instance
  (SymBoolOp bool, Mergeable bool s, UnionMergeable1 bool m) =>
  UnionMergeable1 bool (StateC s m)
  where
  mergeWithStrategy ms (StateC f) = StateC $ mergeWithStrategy (liftMergeStrategy ms) . f
  mrgIfWithStrategy s cond (StateC l) (StateC r) = StateC $ \v -> mrgIfWithStrategy (liftMergeStrategy s) cond (l v) (r v)

instance (MonadUnion bool m, Mergeable bool a) => Mergeable bool (LiftC m a) where
  mergeStrategy = wrapMergeStrategy mergeStrategy1 LiftC (\(LiftC m) -> m)

instance (MonadUnion bool m) => Mergeable1 bool (LiftC m) where
  liftMergeStrategy ms = wrapMergeStrategy (liftMergeStrategy ms) LiftC (\(LiftC m) -> m)

instance (MonadUnion bool m, Mergeable bool a) => SimpleMergeable bool (LiftC m a) where
  mrgIte = mrgIf

instance (MonadUnion bool m) => SimpleMergeable1 bool (LiftC m) where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy


instance (MonadUnion bool m) => UnionOp bool (LiftC m) where
  single x = LiftC $ single x
  guard cond (LiftC l) (LiftC r) = LiftC $ guard cond l r

instance (MonadUnion bool m) => UnionMergeable1 bool (LiftC m) where
  mergeWithStrategy s (LiftC v) = LiftC $ mergeWithStrategy s v
  mrgIfWithStrategy s cond (LiftC l) (LiftC r) = LiftC $ mrgIfWithStrategy s cond l r
