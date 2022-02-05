{-# LANGUAGE StandaloneDeriving #-}

module Match where

import BonsaiTree
import Control.Monad.Except
import GHC.Generics
import GHC.TypeLits
import Grisette.Core
import Grisette.SymPrim.Term
import Pattern
import SyntaxSpec

data PrivateMatchError e
  = PrivateMatchError
  | OriginalError e
  deriving (Eq, Show, Generic)

instance TransformError e (PrivateMatchError e) where
  transformError = OriginalError

deriving instance (Mergeable SymBool e) => Mergeable SymBool (PrivateMatchError e)

bonsaiMatchCustomError :: 
  (KnownNat m, 1 <= m, Mergeable SymBool e, Mergeable SymBool t) =>
  e -> OptimSyntaxSpec m -> [PatternHandler m e t] -> BonsaiTree m -> ExceptT e UnionM t
bonsaiMatchCustomError e stx handlers tree =
  merge $ withExceptT (\case 
    PrivateMatchError -> e
    OriginalError e1 -> e1) $
  foldl (\acc handler -> acc `catchError` \case
    PrivateMatchError -> bonsaiMatchHandler stx handler tree
    e1 -> throwError e1
  ) (throwError PrivateMatchError) handlers

bonsaiMatchHandler ::
  (KnownNat m, 1 <= m, Mergeable SymBool e, Mergeable SymBool t) =>
  OptimSyntaxSpec m ->
  PatternHandler m e t ->
  BonsaiTree m ->
  ExceptT (PrivateMatchError e) UnionM t
bonsaiMatchHandler stx h@(PatternHandler0 p _) tree = do
  b <- bonsaiMatchPattern stx p tree
  merge $ withExceptT transformError $ applyHandler b h
bonsaiMatchHandler stx h@(PatternHandler1 p _) tree = do
  b <- bonsaiMatchPattern stx p tree
  merge $ withExceptT transformError $ applyHandler b h
bonsaiMatchHandler stx h@(PatternHandler2 p _) tree = do
  b <- bonsaiMatchPattern stx p tree
  merge $ withExceptT transformError $ applyHandler b h
bonsaiMatchHandler stx h@(PatternHandler3 p _) tree = do
  b <- bonsaiMatchPattern stx p tree
  merge $ withExceptT transformError $ applyHandler b h

bonsaiMatchPattern ::
  (KnownNat m, 1 <= m, Mergeable SymBool e) =>
  OptimSyntaxSpec m ->
  Pattern n ->
  BonsaiTree m ->
  ExceptT (PrivateMatchError e) UnionM [UnionM (BonsaiTree m)]
bonsaiMatchPattern stx (LiteralPattern str) (BonsaiLeaf sym) =
  mrgGuard
    (Just sym ==~ (conc <$> terminalToBV stx str))
    (mrgSingle [])
    (throwError PrivateMatchError)
bonsaiMatchPattern stx (PairPattern leftp rightp) (BonsaiNode left right) = do
  l <- bonsaiMatchPattern stx leftp #~ left
  r <- bonsaiMatchPattern stx rightp #~ right
  mrgReturn $ l ++ r
bonsaiMatchPattern _ PlaceHolder t = mrgReturn [mrgSingle t]
bonsaiMatchPattern _ _ _ = throwError PrivateMatchError
