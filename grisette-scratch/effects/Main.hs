{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Algebra
import Control.Carrier.Error.Either
import Control.Carrier.State.Strict
import qualified Control.Monad.Except as E
import Grisette
import Control.Carrier.Lift

instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ErrorC e m a)
  where
  mergeStrategy = wrapMergeStrategy mergeStrategy ErrorC (\(ErrorC et) -> et)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ErrorC e m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool e, Mergeable bool a, Functor m) =>
  SimpleMergeable bool (ErrorC e m a)
  where
  mrgIte cond (ErrorC t) (ErrorC f) = ErrorC $ mrgIte cond t f

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool e, Functor m) =>
  SimpleMergeable1 bool (ErrorC e m)

instance
  (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool e, Functor m) =>
  UnionSimpleMergeable1 bool (ErrorC e m)

instance
  (SymBoolOp bool, MonadUnion bool m, Mergeable bool e, Functor m) =>
  MonadUnion bool (ErrorC e m)
  where
  merge (ErrorC et) = ErrorC $ merge et
  mrgReturn et = ErrorC $ mrgReturn et
  mrgIf cond (ErrorC t) (ErrorC f) = ErrorC $ mrgIf cond t f

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateC s m a) where
  mergeStrategy =
    withMergeable @bool @m @(s, a) $
      withMergeable @bool @((->) s) @(m (s, a)) $
        wrapMergeStrategy mergeStrategy StateC (\(StateC f) -> f)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) =>
  Mergeable1 bool (StateC s m) where

instance (SymBoolOp bool, Mergeable bool s, Mergeable bool a, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable bool (StateC s m a) where
    mrgIte cond (StateC t) (StateC f) =
      withUnionSimpleMergeable @bool @m @(s, a) $
        withSimpleMergeable @bool @((->) s) @(m (s, a)) $
          StateC $ mrgIte cond t f

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (StateC s m)

instance
  (SymBoolOp bool, Mergeable bool s, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (StateC s m)

instance
  (SymBoolOp bool, Mergeable bool s, MonadUnion bool m) =>
  MonadUnion bool (StateC s m) where
    merge (StateC f) = StateC $ merge . f
    mrgReturn v = StateC $ \s -> mrgReturn (s, v)
    mrgIf cond (StateC t) (StateC f) = StateC $ \s -> mrgIf cond (t s) (f s)

instance (MonadUnion bool m, Mergeable bool a) => Mergeable bool (LiftC m a) where
  mergeStrategy = withUnionSimpleMergeable @bool @m @a $ wrapMergeStrategy mergeStrategy LiftC (\(LiftC m) -> m)
instance (MonadUnion bool m) => Mergeable1 bool (LiftC m)
instance (MonadUnion bool m, Mergeable bool a) => SimpleMergeable bool (LiftC m a) where
  mrgIte cond (LiftC l) (LiftC r) = LiftC $ mrgIteu1 cond l r
instance (MonadUnion bool m) => SimpleMergeable1 bool (LiftC m)
instance (MonadUnion bool m) => UnionSimpleMergeable1 bool (LiftC m)
instance (MonadUnion bool m) => MonadUnion bool (LiftC m) where
  merge (LiftC v) = LiftC $ merge v
  mrgReturn v = LiftC $ mrgReturn v
  mrgIf cond (LiftC l) (LiftC r) = LiftC $ mrgIf cond l r

v1 :: (SymBoolOp bool, Has (Error VerificationConditions) sig m, MonadUnion bool m) => m ()
v1 = mrgIf (ssymb "a") (throwError AssertionViolation) (return ())

v2 ::
  ( SymBoolOp bool,
    Has (Error VerificationConditions) sig m,
    Has (State SymBool) sig m,
    MonadUnion bool m
  ) =>
  m ()
v2 = do
  modify $ \(x :: SymBool) -> nots x
  mrgIf (ssymb "a") (throwError AssertionViolation) (return ())

main :: IO ()
main = do
  print $ runM $ runError (v1 :: ErrorC VerificationConditions (LiftC UnionM) ())
  print $ runM $ E.runExceptT (v1 :: E.ExceptT VerificationConditions (LiftC UnionM) ())
  print $ runM $ runError $ runState (ssymb "x") (v2 :: StateC SymBool (ErrorC VerificationConditions (LiftC UnionM)) ())
  print $ runM $ runState (ssymb "x") $ runError (v2 :: ErrorC VerificationConditions (StateC SymBool (LiftC UnionM)) ())
