{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where
import Grisette
import Control.Algebra
import Control.Effect.Lift
import qualified Control.Monad.Except as E
import Control.Carrier.Error.Either
import Control.Carrier.State.Strict
import qualified Control.Monad.State.Strict as S

instance (SymBoolOp bool) => Algebra (Lift (UnionMBase bool)) (UnionMBase bool) where
  alg hdl (LiftWith with) = with hdl

v :: E.ExceptT VerificationConditions UnionM ()
v = mrgIf (ssymb "a") (throwError AssertionViolation) (return ())

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


v2 :: (SymBoolOp bool, Has (Error VerificationConditions) sig m, MonadUnion bool m) => m ()
v2 = mrgIf (ssymb "a") (throwError AssertionViolation) (return ())

v3 :: (SymBoolOp bool, Has (Error VerificationConditions) sig m,
  Has (State SymBool) sig m,
  MonadUnion bool m) => m ()
v3 = do
  modify $ \(x :: SymBool) -> nots x
  mrgIf (ssymb "a") (throwError AssertionViolation) (return ())

main :: IO ()
main = do
  print $ runError (v2 :: ErrorC VerificationConditions UnionM ())
  print $ E.runExceptT (v2 :: E.ExceptT VerificationConditions UnionM ())
  print $ runError $ (\m -> S.runStateT m $ ssymb "x") (v3 :: S.StateT SymBool (ErrorC VerificationConditions UnionM) ())
  print $ (\m -> S.runStateT m $ ssymb "x") $ runError (v3 :: ErrorC VerificationConditions (S.StateT SymBool UnionM) ())
