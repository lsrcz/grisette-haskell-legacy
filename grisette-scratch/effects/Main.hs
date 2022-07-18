{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Control.Algebra
import Control.Carrier.Error.Either
import qualified Control.Carrier.Error.Church as EC
import Control.Carrier.State.Strict
import qualified Control.Monad.Except as E
import Grisette
import Control.Carrier.Lift
import Instances ()
import Debug.Trace

-- We believe that UnionM should be implemented as a monad rather than an effect,
-- while we can still use it with effect systems for the composability.

-- The UnionM monad is designed to be the innermost monad in the transformer stack like IO monad,
-- and it should be used as the base computation with 'Lift' handlers in effect systems.
-- The simple reason is that MonadUnion models fully-isolated multipath execution,
-- and there is no transformer that transforms an arbitrary monad into a MonadUnion.
-- Similarly we cannot have a UnionM effect that composes with other effects arbitrarily.
-- This is the shared limitation of mtl and effect systems.

-- After defining MonadUnion instances for 'LiftC' / 'StateC' / 'ErrorC'
-- as how the MonadIO instances are defined for them,
-- we can use 'UnionM' monad in 'LiftC' with various effects.
--
-- We can use them with 'UnionM' monad in 'LiftC' as an effect carrier,
-- and compose with other effect handlers nicely.

v1 :: (SymBoolOp bool, Has (Error VerificationConditions) sig m, UnionLike bool m) => m ()
v1 = mrgIf (ssymb "a") (throwError AssertionViolation) (return ())

v2 ::
  ( SymBoolOp bool,
    Has (Error VerificationConditions) sig m,
    Has (State SymBool) sig m,
    Has (State SymInteger) sig m,
    UnionLike bool m
  ) =>
  m [bool]
v2 = do
  trace "x" $ modify $ \(x :: SymBool) -> nots x
  modify $ \(x :: SymInteger) -> x + 1
  mrgIf (ssymb "a") (throwError AssertionViolation) (return ())
  mrgIf (ssymb "b") (return ["c"]) (return ["d"])

v3 ::
  ( SymBoolOp bool,
    Has (Error VerificationConditions) sig m,
    Has (State SymBool) sig m,
    Has (State SymInteger) sig m,
    UnionLike bool m
  ) =>
  SymInteger -> m [bool]
v3 v = trace "y" $ do
  modify $ \(x :: SymBool) -> trace "z" $ nots x
  modify $ \(x :: SymInteger) -> x + v
  mrgIf (ssymb "a") (throwError AssertionViolation) (return ())
  trace "x" $ mrgIf (ssymb "b") (return ["c"]) (return ["d"])


v4 ::
  ( Has (Error VerificationConditions) sig m,
    UnionLike SymBool m
  ) =>
  SymInteger -> m SymInteger
v4 v = trace "y" $ do
  mrgIf (ssymb "a") (throwError AssertionViolation) (return ())
  trace "x" $ mrgIf (ssymb "b") (return v) (return $ v + 1)


main :: IO ()
main = do
  print $ runM $ runError (v1 :: ErrorC VerificationConditions (LiftC UnionM) ())
  -- UMrg (If a (Single (Left AssertionViolation)) (Single (Right ())))
  print $ runM $ E.runExceptT (v1 :: E.ExceptT VerificationConditions (LiftC UnionM) ())
  -- UMrg (If a (Single (Left AssertionViolation)) (Single (Right ())))
  print $ runM $ runError $ runState (ssymb "x") $ runState (ssymb "y")
    (v2 :: StateC SymInteger (StateC SymBool (ErrorC VerificationConditions (LiftC UnionM))) [SymBool])
  -- UMrg (If a (Single (Left AssertionViolation)) (Single (Right ((! x),((+ 1I y),[(ite b c d)])))))
  print $ runM $ runState (ssymb "x") $ runError $ runState (ssymb "y")
    (v2 :: StateC SymInteger (ErrorC VerificationConditions (StateC SymBool (LiftC UnionM))) [SymBool])
  -- UMrg (If a (Single ((! x),Left AssertionViolation)) (Single ((! x),Right ((+ 1I y),[(ite b c d)]))))

  print $ runM $ EC.runError (\_ -> mrgReturn (1 :: Integer)) (\_ -> mrgReturn 2)
    (v1 :: EC.ErrorC VerificationConditions (LiftC UnionM) ())

  putStrLn "xxx"
  print $ runM $ EC.runError (\x -> trace "r1" $ mrgReturn . Left $ x) (\x -> trace "r2" $ mrgReturn . Right $ x) $ runState (ssymb "x") $ runState (ssymb "y")
    (v3 1 >> v3 2 >> v3 3 :: StateC SymInteger (StateC SymBool (EC.ErrorC VerificationConditions (LiftC UnionM))) [SymBool])
  putStrLn "yyy"
  print $ runM $ runError $ runState (ssymb "x") $ runState (ssymb "y")
    (v3 1 >> v3 2 >> v3 3 :: StateC SymInteger (StateC SymBool (ErrorC VerificationConditions (LiftC UnionM))) [SymBool])

  putStrLn "zzz"
  print $ runM $ EC.runError (\x -> trace "r1" $ mrgReturn . Left $ x) (\x -> trace "r2" $ mrgReturn . Right $ x) $
    (v4 1 >>= v4 >>= v4 :: EC.ErrorC VerificationConditions (LiftC UnionM) SymInteger)
