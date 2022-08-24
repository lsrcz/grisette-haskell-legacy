{-# LANGUAGE StandaloneDeriving #-}

module Bonsai.Match (bonsaiMatchCustomError) where

import Bonsai.BonsaiTree
import Bonsai.Pattern
import Control.Monad.Except
import GHC.Generics
import Grisette

data PrivateMatchError e
  = PrivateMatchError
  | OriginalError e
  deriving (Eq, Show, Generic)

instance TransformError e (PrivateMatchError e) where
  transformError = OriginalError

deriving via (Default (PrivateMatchError e)) instance (Mergeable SymBool e) => Mergeable SymBool (PrivateMatchError e)

bonsaiMatchCustomError ::
  (SEq SymBool m, Mergeable SymBool m, Mergeable SymBool e, Mergeable SymBool t) =>
  e ->
  [PatternHandler m e t] ->
  BonsaiTree m ->
  CBMCExceptT e UnionM t
bonsaiMatchCustomError e handlers tree =
  merge $
    withCBMCExceptT (\case PrivateMatchError -> e; OriginalError e1 -> e1) $
      foldl
        ( \acc handler ->
            acc `catchError` \case
              PrivateMatchError -> bonsaiMatchHandler handler tree
              e1 -> throwError e1
        )
        (throwError PrivateMatchError)
        handlers
{-# INLINE bonsaiMatchCustomError #-}

bonsaiMatchHandler ::
  (SEq SymBool m, Mergeable SymBool m, Mergeable SymBool e, Mergeable SymBool t) =>
  PatternHandler m e t ->
  BonsaiTree m ->
  CBMCExceptT (PrivateMatchError e) UnionM t
bonsaiMatchHandler h@(PatternHandler0 p _) tree = do
  b <- bonsaiMatchPattern p tree
  merge $ withCBMCExceptT transformError $ applyHandler b h
bonsaiMatchHandler h@(PatternHandler1 p _) tree = do
  b <- bonsaiMatchPattern p tree
  merge $ withCBMCExceptT transformError $ applyHandler b h
bonsaiMatchHandler h@(PatternHandler2 p _) tree = do
  b <- bonsaiMatchPattern p tree
  merge $ withCBMCExceptT transformError $ applyHandler b h
bonsaiMatchHandler h@(PatternHandler3 p _) tree = do
  b <- bonsaiMatchPattern p tree
  merge $ withCBMCExceptT transformError $ applyHandler b h
bonsaiMatchHandler h@(PatternHandler4 p _) tree = do
  b <- bonsaiMatchPattern p tree
  merge $ withCBMCExceptT transformError $ applyHandler b h
bonsaiMatchHandler h@(PatternHandler5 p _) tree = do
  b <- bonsaiMatchPattern p tree
  merge $ withCBMCExceptT transformError $ applyHandler b h
{-# INLINE bonsaiMatchHandler #-}

bonsaiMatchPattern ::
  (SEq SymBool m, Mergeable SymBool m, Mergeable SymBool e) =>
  Pattern m n ->
  BonsaiTree m ->
  CBMCExceptT (PrivateMatchError e) UnionM [UnionM (BonsaiTree m)]
bonsaiMatchPattern (LiteralPattern lit) (BonsaiLeaf sym) =
  mrgIf (sym ==~ lit) (mrgReturn []) (throwError PrivateMatchError)
bonsaiMatchPattern (PairPattern leftp rightp) (BonsaiNode left right) = do
  l <- bonsaiMatchPattern leftp #~ left
  r <- bonsaiMatchPattern rightp #~ right
  mrgReturn $ l ++ r
bonsaiMatchPattern PlaceHolder t = mrgReturn [mrgReturn t]
bonsaiMatchPattern _ _ = throwError PrivateMatchError
{-# INLINE bonsaiMatchPattern #-}
