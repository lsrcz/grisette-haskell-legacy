{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
  ( identity,
    identityWithTypeRep,
    introSupportedPrimConstraint,
    extractSymbolicsTerm,
    castTerm,
    pformat,
    termSize,
    termsSize,
  )
where

import Control.Monad.State
import Data.HashMap.Strict as M
import Data.HashSet as S
import Data.Interned
import Data.Typeable
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term

identity :: Term t -> Id
identity (ConcTerm i _) = i
identity (SymbTerm i _) = i
identity (UnaryTerm i _ _) = i
identity (BinaryTerm i _ _ _) = i
identity (TernaryTerm i _ _ _ _) = i
{-# INLINE identity #-}

identityWithTypeRep :: forall t. Term t -> (TypeRep, Id)
identityWithTypeRep (ConcTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (SymbTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (UnaryTerm i _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (BinaryTerm i _ _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (TernaryTerm i _ _ _ _) = (typeRep (Proxy @t), i)
{-# INLINE identityWithTypeRep #-}

introSupportedPrimConstraint :: forall t a. Term t -> ((SupportedPrim t) => a) -> a
introSupportedPrimConstraint ConcTerm {} x = x
introSupportedPrimConstraint SymbTerm {} x = x
introSupportedPrimConstraint UnaryTerm {} x = x
introSupportedPrimConstraint BinaryTerm {} x = x
introSupportedPrimConstraint TernaryTerm {} x = x
{-# INLINE introSupportedPrimConstraint #-}

extractSymbolicsSomeTerm :: SomeTerm -> S.HashSet TermSymbol
extractSymbolicsSomeTerm t1 = evalState (gocached t1) M.empty
  where
    gocached :: SomeTerm -> State (M.HashMap SomeTerm (S.HashSet TermSymbol)) (S.HashSet TermSymbol)
    gocached t = do
      v <- gets (M.lookup t)
      case v of
        Just x -> return x
        Nothing -> do
          res <- go t
          st <- get
          put $ M.insert t res st
          return res
    go :: SomeTerm -> State (M.HashMap SomeTerm (S.HashSet TermSymbol)) (S.HashSet TermSymbol)
    go (SomeTerm ConcTerm {}) = return $ S.empty
    go (SomeTerm (SymbTerm _ symb)) = return $ S.singleton symb
    go (SomeTerm (UnaryTerm _ _ arg)) = gocached (SomeTerm arg)
    go (SomeTerm (BinaryTerm _ _ arg1 arg2)) = do
      r1 <- gocached (SomeTerm arg1)
      r2 <- gocached (SomeTerm arg2)
      return $ r1 <> r2
    go (SomeTerm (TernaryTerm _ _ arg1 arg2 arg3)) = do
      r1 <- gocached (SomeTerm arg1)
      r2 <- gocached (SomeTerm arg2)
      r3 <- gocached (SomeTerm arg3)
      return $ r1 <> r2 <> r3
{-# INLINEABLE extractSymbolicsSomeTerm #-}

extractSymbolicsTerm :: (SupportedPrim a) => Term a -> S.HashSet TermSymbol
extractSymbolicsTerm t = extractSymbolicsSomeTerm (SomeTerm t)
{-# INLINE extractSymbolicsTerm #-}

castTerm :: forall a b. (Typeable b) => Term a -> Maybe (Term b)
castTerm t@ConcTerm {} = cast t
castTerm t@SymbTerm {} = cast t
castTerm t@UnaryTerm {} = cast t
castTerm t@BinaryTerm {} = cast t
castTerm t@TernaryTerm {} = cast t
{-# INLINE castTerm #-}

pformat :: forall t. (SupportedPrim t) => Term t -> String
pformat (ConcTerm _ t) = pformatConc t
pformat (SymbTerm _ (TermSymbol _ symb)) = pformatSymb (Proxy @t) symb
pformat (UnaryTerm _ tag arg1) = pformatUnary tag arg1
pformat (BinaryTerm _ tag arg1 arg2) = pformatBinary tag arg1 arg2
pformat (TernaryTerm _ tag arg1 arg2 arg3) = pformatTernary tag arg1 arg2 arg3
{-# INLINE pformat #-}

termsSize :: [Term a] -> Int
termsSize terms = S.size $ execState (traverse go terms) S.empty
  where
    exists t = gets (S.member (SomeTerm t))
    add t = modify' (S.insert (SomeTerm t))
    go :: forall b. Term b -> State (S.HashSet SomeTerm) ()
    go t@ConcTerm {} = add t
    go t@SymbTerm {} = add t
    go t@(UnaryTerm _ _ arg) = do
      b <- exists t
      if b
        then return ()
        else do
          add t
          go arg
    go t@(BinaryTerm _ _ arg1 arg2) = do
      b <- exists t
      if b
        then return ()
        else do
          add t
          go arg1
          go arg2
    go t@(TernaryTerm _ _ arg1 arg2 arg3) = do
      b <- exists t
      if b
        then return ()
        else do
          add t
          go arg1
          go arg2
          go arg3
{-# INLINEABLE termsSize #-}

termSize :: Term a -> Int
termSize term = termsSize [term]
{-# INLINE termSize #-}
