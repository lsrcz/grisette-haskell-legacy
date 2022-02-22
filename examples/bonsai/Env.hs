module Env where

import BonsaiTree
import Control.Monad.Except
import Error
import GHC.TypeNats
import Grisette.Core
import Grisette.SymPrim.Term

type EnvSingle n t = [(SymUnsignedBV n, UnionM t)]

type Env n t = UnionM (EnvSingle n t)

envAdd :: (Mergeable SymBool t, KnownNat n, 1 <= n) => Env n t -> SymUnsignedBV n -> UnionM t -> Env n t
envAdd env k v = do
  e <- env
  mrgReturn $ (k, v) : e

extractName ::
  (KnownNat n, 1 <= n) =>
  BonsaiError ->
  UnionM (BonsaiTree (SymUnsignedBV n)) ->
  ExceptT BonsaiError UnionM (SymUnsignedBV n)
extractName err m = do
  t <- lift m
  case t of
    BonsaiLeaf sym -> mrgReturn sym
    BonsaiNode _ _ -> throwError err

envAddTree ::
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  BonsaiError ->
  Env n t ->
  UnionM (BonsaiTree (SymUnsignedBV n)) ->
  UnionM t ->
  ExceptT BonsaiError UnionM (Env n t)
envAddTree err env t v = do
  name <- extractName err t
  mrgReturn $ envAdd env name v

envResolve ::
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  BonsaiError ->
  Env n t ->
  SymUnsignedBV n ->
  ExceptT BonsaiError UnionM t
envResolve err env k = do
  e <- lift env
  envResolveSingle e
  where
    envResolveSingle [] = throwError err
    envResolveSingle ((n, v) : xs) = mrgIf (n ==~ k) (lift v) $ envResolveSingle xs

envResolveU ::
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  BonsaiError ->
  Env n t ->
  SymUnsignedBV n ->
  ExceptT BonsaiError UnionM (UnionM t)
envResolveU err env k = do
  e <- lift env
  envResolveSingle e
  where
    envResolveSingle [] = throwError err
    envResolveSingle ((n, v) : xs) = mrgIf (n ==~ k) (return v) $ envResolveSingle xs

envResolve' ::
  forall n t.
  (Mergeable SymBool t, KnownNat n, 1 <= n) =>
  Int ->
  BonsaiError ->
  Env n t ->
  SymUnsignedBV n ->
  ExceptT BonsaiError UnionM t
envResolve' fuel err env k = do
  e <- lift env
  envResolveSingle 0 e
  where
    envResolveSingle :: Int -> EnvSingle n t -> ExceptT BonsaiError UnionM t
    envResolveSingle _ [] = throwError err
    envResolveSingle x ((n, v) : xs) =
      if x > fuel
        then throwError BonsaiRecursionError
        else mrgIf (n ==~ k) (lift v) $ envResolveSingle (x + 1) xs
