module Bonsai.Env (Env, EnvSingle, envAdd, extractName, envAddTree, envResolveU, envResolve') where

import Bonsai.BonsaiTree
import Control.Monad.Except
import GHC.TypeNats
import Grisette

type EnvSingle n t = [(SymWordN n, UnionM t)]

type Env n t = UnionM (EnvSingle n t)

envAdd :: (Mergeable SymBool t, KnownNat n, 1 <= n) => Env n t -> SymWordN n -> UnionM t -> Env n t
envAdd env k v = do
  e <- env
  mrgReturn $ (k, v) : e
{-# INLINE envAdd #-}

extractName ::
  (KnownNat n, 1 <= n) =>
  BonsaiError ->
  UnionM (BonsaiTree (SymWordN n)) ->
  ExceptT BonsaiError UnionM (SymWordN n)
extractName err m = do
  t <- lift m
  case t of
    BonsaiLeaf sym -> mrgReturn sym
    BonsaiNode _ _ -> throwError err
{-# INLINE extractName #-}

envAddTree ::
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  BonsaiError ->
  Env n t ->
  UnionM (BonsaiTree (SymWordN n)) ->
  UnionM t ->
  ExceptT BonsaiError UnionM (Env n t)
envAddTree err env t v = do
  nm <- extractName err t
  mrgReturn $ envAdd env nm v
{-# INLINE envAddTree #-}

envResolveU ::
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  BonsaiError ->
  Env n t ->
  SymWordN n ->
  ExceptT BonsaiError UnionM (UnionM t)
envResolveU err env k = do
  e <- lift env
  envResolveSingle e
  where
    envResolveSingle [] = throwError err
    envResolveSingle ((n, v) : xs) = mrgIf (n ==~ k) (return v) $ envResolveSingle xs
{-# INLINE envResolveU #-}

envResolve' ::
  forall n t.
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  Int ->
  BonsaiError ->
  Env n t ->
  SymWordN n ->
  ExceptT BonsaiError UnionM t
envResolve' fuel err env k = do
  e <- lift env
  envResolveSingle 0 e
  where
    envResolveSingle _ [] = throwError err
    envResolveSingle x ((n, v) : xs) =
      if x > fuel
        then throwError BonsaiRecursionError
        else mrgIf (n ==~ k) (lift v) $ envResolveSingle (x + 1) xs
{-# INLINE envResolve' #-}
