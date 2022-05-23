{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Grisette.Control.Monad.Union
  ( MonadUnion,
    mrgReturnWithStrategy,
    mrgBindWithStrategy,
    mrgReturn,
    (>>=~),
    getSingle,
  )
where

import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp

-- $setup
-- >>> import Grisette.Core
-- >>> import Grisette.IR.SymPrim

-- | Class for monads that support union-like operations and 'Mergeable' knowledge propagation.
type MonadUnion bool u = (UnionMergeable1 bool u, Monad u)

-- | 'return' with 'Mergeable' knowledge propagation.
mrgReturnWithStrategy :: (MonadUnion bool u) => MergeStrategy bool a -> a -> u a
mrgReturnWithStrategy s = mergeWithStrategy s . return

-- | '>>=' with 'Mergeable' knowledge propagation.
mrgBindWithStrategy :: (MonadUnion bool u) => MergeStrategy bool b -> u a -> (a -> u b) -> u b
mrgBindWithStrategy s a f = mergeWithStrategy s $ a >>= f

-- | 'return' with 'Mergeable' knowledge propagation.
mrgReturn :: (MonadUnion bool u, Mergeable bool a) => a -> u a
mrgReturn = merge . return

-- | '>>=' with 'Mergeable' knowledge propagation.
(>>=~) :: (MonadUnion bool u, Mergeable bool b) => u a -> (a -> u b) -> u b
a >>=~ f = merge $ a >>= f

-- | Extract the value from a union-like monad if the value has a simply mergeable type.
--
-- 'Grisette.Data.Class.UnionOp.guard' will not merge the results.
-- 'getSingle' will merge it and extract the single value.
--
-- >>> guard (ssymb "a") (return $ ssymb "b") (return $ ssymb "c") :: UnionM SymBool
-- UAny (Guard a (Single b) (Single c))
-- >>> getSingle $ (guard (ssymb "a") (return $ ssymb "b") (return $ ssymb "c") :: UnionM SymBool)
-- (ite a b c)

getSingle :: forall bool u a. (SimpleMergeable bool a, UnionMergeable1 bool u, UnionOp bool u) => u a -> a
getSingle u = case merge u of
  SingleU x -> x
  _ -> error "Should not happen"
