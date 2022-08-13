{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
  ( constructUnary,
    constructBinary,
    constructTernary,
    concTerm,
    symbTerm,
    ssymbTerm,
    isymbTerm,
    sinfosymbTerm,
    iinfosymbTerm,
    notTerm,
  )
where

import Control.DeepSeq
import Data.Array
import qualified Data.HashMap.Strict as M
import Data.Hashable
import Data.IORef (atomicModifyIORef')
import Data.Interned
import Data.Interned.Internal
import Data.Typeable
import GHC.IO (unsafeDupablePerformIO)
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Language.Haskell.TH.Syntax

internTerm :: forall t. (SupportedPrim t) => Uninterned (Term t) -> Term t
internTerm !bt = unsafeDupablePerformIO $ atomicModifyIORef' slot go
  where
    slot = getCache cache ! r
    !dt = describe bt
    !hdt = hash dt
    !wid = cacheWidth dt
    r = hdt `mod` wid
    go (CacheState i m) = case M.lookup dt m of
      Nothing -> let t = identify (wid * i + r) bt in (CacheState (i + 1) (M.insert dt t m), t)
      Just t -> (CacheState i m, t)

constructUnary ::
  forall tag arg t.
  (SupportedPrim t, UnaryOp tag arg t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg ->
  Term t
constructUnary tag tm = let x = internTerm $ UUnaryTerm tag tm in x
{-# INLINE constructUnary #-}

constructBinary ::
  forall tag arg1 arg2 t.
  (SupportedPrim t, BinaryOp tag arg1 arg2 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term t
constructBinary tag tm1 tm2 = internTerm $ UBinaryTerm tag tm1 tm2
{-# INLINE constructBinary #-}

constructTernary ::
  forall tag arg1 arg2 arg3 t.
  (SupportedPrim t, TernaryOp tag arg1 arg2 arg3 t, Typeable tag, Typeable t, Show tag) =>
  tag ->
  Term arg1 ->
  Term arg2 ->
  Term arg3 ->
  Term t
constructTernary tag tm1 tm2 tm3 = internTerm $ UTernaryTerm tag tm1 tm2 tm3
{-# INLINE constructTernary #-}

concTerm :: (SupportedPrim t, Typeable t, Hashable t, Eq t, Show t) => t -> Term t
concTerm t = internTerm $ UConcTerm t
{-# INLINE concTerm #-}

symbTerm :: forall t. (SupportedPrim t, Typeable t) => Symbol -> Term t
symbTerm t = internTerm $ USymbTerm (TermSymbol (Proxy @t) t)
{-# INLINE symbTerm #-}

ssymbTerm :: (SupportedPrim t, Typeable t) => String -> Term t
ssymbTerm = symbTerm . SimpleSymbol
{-# INLINE ssymbTerm #-}

isymbTerm :: (SupportedPrim t, Typeable t) => String -> Int -> Term t
isymbTerm str idx = symbTerm $ IndexedSymbol str idx
{-# INLINE isymbTerm #-}

sinfosymbTerm :: (SupportedPrim t, Typeable t, Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> a -> Term t
sinfosymbTerm s info = symbTerm $ WithInfo (SimpleSymbol s) info
{-# INLINE sinfosymbTerm #-}

iinfosymbTerm :: (SupportedPrim t, Typeable t, Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> Int -> a -> Term t
iinfosymbTerm str idx info = symbTerm $ WithInfo (IndexedSymbol str idx) info
{-# INLINE iinfosymbTerm #-}

notTerm :: Term Bool -> Term Bool
notTerm = internTerm . UNotTerm
{-# INLINE notTerm #-}