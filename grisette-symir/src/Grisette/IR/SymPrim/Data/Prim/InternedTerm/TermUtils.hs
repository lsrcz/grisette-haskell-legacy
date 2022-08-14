{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

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
identity (NotTerm i _) = i
identity (OrTerm i _ _) = i
identity (AndTerm i _ _) = i
identity (EqvTerm i _ _) = i
identity (ITETerm i _ _ _) = i
identity (AddNumTerm i _ _) = i
identity (UMinusNumTerm i _) = i
identity (TimesNumTerm i _ _) = i
identity (AbsNumTerm i _) = i
identity (SignumNumTerm i _) = i
identity (LTNumTerm i _ _) = i
identity (LENumTerm i _ _) = i
{-# INLINE identity #-}

identityWithTypeRep :: forall t. Term t -> (TypeRep, Id)
identityWithTypeRep (ConcTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (SymbTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (UnaryTerm i _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (BinaryTerm i _ _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (TernaryTerm i _ _ _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (NotTerm i _) = (typeRep (Proxy @Bool), i)
identityWithTypeRep (OrTerm i _ _) = (typeRep (Proxy @Bool), i)
identityWithTypeRep (AndTerm i _ _) = (typeRep (Proxy @Bool), i)
identityWithTypeRep (EqvTerm i _ _) = (typeRep (Proxy @Bool), i)
identityWithTypeRep (ITETerm i _ _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (AddNumTerm i _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (UMinusNumTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (TimesNumTerm i _ _) = (typeRep (Proxy @t), i)
identityWithTypeRep (AbsNumTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (SignumNumTerm i _) = (typeRep (Proxy @t), i)
identityWithTypeRep (LTNumTerm i _ _) = (typeRep (Proxy @Bool), i)
identityWithTypeRep (LENumTerm i _ _) = (typeRep (Proxy @Bool), i)
{-# INLINE identityWithTypeRep #-}

introSupportedPrimConstraint :: forall t a. Term t -> ((SupportedPrim t) => a) -> a
introSupportedPrimConstraint ConcTerm {} x = x
introSupportedPrimConstraint SymbTerm {} x = x
introSupportedPrimConstraint UnaryTerm {} x = x
introSupportedPrimConstraint BinaryTerm {} x = x
introSupportedPrimConstraint TernaryTerm {} x = x
introSupportedPrimConstraint NotTerm {} x = x
introSupportedPrimConstraint OrTerm {} x = x
introSupportedPrimConstraint AndTerm {} x = x
introSupportedPrimConstraint EqvTerm {} x = x
introSupportedPrimConstraint ITETerm {} x = x
introSupportedPrimConstraint AddNumTerm {} x = x
introSupportedPrimConstraint UMinusNumTerm {} x = x
introSupportedPrimConstraint TimesNumTerm {} x = x
introSupportedPrimConstraint AbsNumTerm {} x = x
introSupportedPrimConstraint SignumNumTerm {} x = x
introSupportedPrimConstraint LTNumTerm {} x = x
introSupportedPrimConstraint LENumTerm {} x = x
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
    go (SomeTerm ConcTerm {}) = return S.empty
    go (SomeTerm (SymbTerm _ symb)) = return $ S.singleton symb
    go (SomeTerm (UnaryTerm _ _ arg)) = goUnary arg
    go (SomeTerm (BinaryTerm _ _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (TernaryTerm _ _ arg1 arg2 arg3)) = goTernary arg1 arg2 arg3
    go (SomeTerm (NotTerm _ arg)) = gocached (SomeTerm arg)
    go (SomeTerm (OrTerm _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (AndTerm _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (EqvTerm _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (ITETerm _ cond arg1 arg2)) = goTernary cond arg1 arg2
    go (SomeTerm (AddNumTerm _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (UMinusNumTerm _ arg)) = gocached (SomeTerm arg)
    go (SomeTerm (TimesNumTerm _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (AbsNumTerm _ arg)) = gocached (SomeTerm arg)
    go (SomeTerm (SignumNumTerm _ arg)) = gocached (SomeTerm arg)
    go (SomeTerm (LTNumTerm _ arg1 arg2)) = goBinary arg1 arg2
    go (SomeTerm (LENumTerm _ arg1 arg2)) = goBinary arg1 arg2
    goUnary arg = gocached (SomeTerm arg)
    goBinary arg1 arg2 = do
      r1 <- gocached (SomeTerm arg1)
      r2 <- gocached (SomeTerm arg2)
      return $ r1 <> r2
    goTernary arg1 arg2 arg3 = do
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
castTerm t@NotTerm {} = cast t
castTerm t@OrTerm {} = cast t
castTerm t@AndTerm {} = cast t
castTerm t@EqvTerm {} = cast t
castTerm t@ITETerm {} = cast t
castTerm t@AddNumTerm {} = cast t
castTerm t@UMinusNumTerm {} = cast t
castTerm t@TimesNumTerm {} = cast t
castTerm t@AbsNumTerm {} = cast t
castTerm t@SignumNumTerm {} = cast t
castTerm t@LTNumTerm {} = cast t
castTerm t@LENumTerm {} = cast t
{-# INLINE castTerm #-}

pformat :: forall t. (SupportedPrim t) => Term t -> String
pformat (ConcTerm _ t) = pformatConc t
pformat (SymbTerm _ (TermSymbol _ symb)) = pformatSymb (Proxy @t) symb
pformat (UnaryTerm _ tag arg1) = pformatUnary tag arg1
pformat (BinaryTerm _ tag arg1 arg2) = pformatBinary tag arg1 arg2
pformat (TernaryTerm _ tag arg1 arg2 arg3) = pformatTernary tag arg1 arg2 arg3
pformat (NotTerm _ arg) = "(! " ++ pformat arg ++ ")"
pformat (OrTerm _ arg1 arg2) = "(|| " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (AndTerm _ arg1 arg2) = "(&& " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (EqvTerm _ arg1 arg2) = "(= " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (ITETerm _ cond arg1 arg2) = "(ite " ++ pformat cond ++ " " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (AddNumTerm _ arg1 arg2) = "(+ " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (UMinusNumTerm _ arg) = "(- " ++ pformat arg ++ ")"
pformat (TimesNumTerm _ arg1 arg2) = "(* " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (AbsNumTerm _ arg) = "(abs " ++ pformat arg ++ ")"
pformat (SignumNumTerm _ arg) = "(signum " ++ pformat arg ++ ")"
pformat (LTNumTerm _ arg1 arg2) = "(< " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
pformat (LENumTerm _ arg1 arg2) = "(<= " ++ pformat arg1 ++ " " ++ pformat arg2 ++ ")"
{-# INLINE pformat #-}

termsSize :: [Term a] -> Int
termsSize terms = S.size $ execState (traverse go terms) S.empty
  where
    exists t = gets (S.member (SomeTerm t))
    add t = modify' (S.insert (SomeTerm t))
    go :: forall b. Term b -> State (S.HashSet SomeTerm) ()
    go t@ConcTerm {} = add t
    go t@SymbTerm {} = add t
    go t@(UnaryTerm _ _ arg) = goUnary t arg
    go t@(BinaryTerm _ _ arg1 arg2) = goBinary t arg1 arg2
    go t@(TernaryTerm _ _ arg1 arg2 arg3) = goTernary t arg1 arg2 arg3
    go t@(NotTerm _ arg) = goUnary t arg
    go t@(OrTerm _ arg1 arg2) = goBinary t arg1 arg2
    go t@(AndTerm _ arg1 arg2) = goBinary t arg1 arg2
    go t@(EqvTerm _ arg1 arg2) = goBinary t arg1 arg2
    go t@(ITETerm _ cond arg1 arg2) = goTernary t cond arg1 arg2
    go t@(AddNumTerm _ arg1 arg2) = goBinary t arg1 arg2
    go t@(UMinusNumTerm _ arg) = goUnary t arg
    go t@(TimesNumTerm _ arg1 arg2) = goBinary t arg1 arg2
    go t@(AbsNumTerm _ arg) = goUnary t arg
    go t@(SignumNumTerm _ arg) = goUnary t arg
    go t@(LTNumTerm _ arg1 arg2) = goBinary t arg1 arg2
    go t@(LENumTerm _ arg1 arg2) = goBinary t arg1 arg2
    goUnary :: forall a b. (SupportedPrim a) => Term a -> Term b -> State (S.HashSet SomeTerm) ()
    goUnary t arg = do
      b <- exists t
      if b
        then return ()
        else do
          add t
          go arg
    goBinary :: forall a b c. (SupportedPrim a, SupportedPrim b) =>
      Term a -> Term b -> Term c -> State (S.HashSet SomeTerm) ()
    goBinary t arg1 arg2 = do
      b <- exists t
      if b
        then return ()
        else do
          add t
          go arg1
          go arg2
    goTernary :: forall a b c d. (SupportedPrim a, SupportedPrim b, SupportedPrim c) =>
      Term a -> Term b -> Term c -> Term d -> State (S.HashSet SomeTerm) ()
    goTernary t arg1 arg2 arg3 = do
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
