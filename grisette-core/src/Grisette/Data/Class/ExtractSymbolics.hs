{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.ExtractSymbolics
  ( ExtractSymbolics (..),
  )
where

import Control.Monad.Coroutine
import Control.Monad.Except
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import Generics.Deriving
import Control.Monad.Identity

-- $setup
-- >>> import Grisette.Core
-- >>> import Grisette.IR.SymPrim
-- >>> import Data.HashSet as HashSet
-- >>> import Data.List (sort)

-- | Extracts all the symbolic variables that are transitively contained in the given value.
--  
-- >>> extractSymbolics ("a" :: SymBool) :: HashSet TermSymbol
-- fromList [a :: Bool]
-- 
-- >>> :{
--   sort $ 
--     HashSet.toList $
--       extractSymbolics (mrgIf "a" (mrgReturn ["b"]) (mrgReturn ["c", "d"]) :: UnionM [SymBool]) :: [TermSymbol]
-- :}
-- [a :: Bool,b :: Bool,c :: Bool,d :: Bool]
class (Monoid symbolSet) => ExtractSymbolics symbolSet a where
  extractSymbolics :: a -> symbolSet

instance (Generic a, Monoid symbolSet, ExtractSymbolics' symbolSet (Rep a)) => ExtractSymbolics symbolSet (Default a) where
  extractSymbolics = extractSymbolics' . from . unDefault

class (Monoid symbolSet) => ExtractSymbolics' symbolSet a where
  extractSymbolics' :: a c -> symbolSet

instance (Monoid symbolSet) => ExtractSymbolics' symbolSet U1 where
  extractSymbolics' _ = mempty

instance (Monoid symbolSet, ExtractSymbolics symbolSet c) => ExtractSymbolics' symbolSet (K1 i c) where
  extractSymbolics' = extractSymbolics . unK1

instance (Monoid symbolSet, ExtractSymbolics' symbolSet a) => ExtractSymbolics' symbolSet (M1 i c a) where
  extractSymbolics' = extractSymbolics' . unM1

instance
  (Monoid symbolSet, ExtractSymbolics' symbolSet a, ExtractSymbolics' symbolSet b) =>
  ExtractSymbolics' symbolSet (a :+: b)
  where
  extractSymbolics' (L1 l) = extractSymbolics' l
  extractSymbolics' (R1 r) = extractSymbolics' r

instance
  (Monoid symbolSet, ExtractSymbolics' symbolSet a, ExtractSymbolics' symbolSet b) =>
  ExtractSymbolics' symbolSet (a :*: b)
  where
  extractSymbolics' (l :*: r) = extractSymbolics' l <> extractSymbolics' r

-- instances

-- Bool
instance (Monoid symbolSet) => ExtractSymbolics symbolSet Bool where
  extractSymbolics _ = mempty

-- Integer
instance (Monoid symbolSet) => ExtractSymbolics symbolSet Integer where
  extractSymbolics _ = mempty

-- Char
instance (Monoid symbolSet) => ExtractSymbolics symbolSet Char where
  extractSymbolics _ = mempty

-- ()
instance (Monoid symbolSet) => ExtractSymbolics symbolSet () where
  extractSymbolics _ = mempty

-- ByteString
instance (Monoid symbolSet) => ExtractSymbolics symbolSet B.ByteString where
  extractSymbolics _ = mempty

-- Either
deriving via
  (Default (Either a b))
  instance
    (Monoid symbolSet, ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet b) =>
    ExtractSymbolics symbolSet (Either a b)

-- Maybe
deriving via
  (Default (Maybe a))
  instance
    (Monoid symbolSet, ExtractSymbolics symbolSet a) => ExtractSymbolics symbolSet (Maybe a)

-- List
deriving via
  (Default [a])
  instance
    (Monoid symbolSet, ExtractSymbolics symbolSet a) => ExtractSymbolics symbolSet [a]

-- (,)
deriving via
  (Default (a, b))
  instance
    (Monoid symbolSet, ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet b) =>
    ExtractSymbolics symbolSet (a, b)

-- (,,)
deriving via
  (Default (a, b, c))
  instance
    (Monoid symbolSet, ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet b, ExtractSymbolics symbolSet c) =>
    ExtractSymbolics symbolSet (a, b, c)

-- MaybeT
instance (Monoid symbolSet, ExtractSymbolics symbolSet (m (Maybe a))) => ExtractSymbolics symbolSet (MaybeT m a) where
  extractSymbolics (MaybeT v) = extractSymbolics v

-- ExceptT
instance
  (Monoid symbolSet, ExtractSymbolics symbolSet (m (Either e a))) =>
  ExtractSymbolics symbolSet (ExceptT e m a)
  where
  extractSymbolics (ExceptT v) = extractSymbolics v

-- Coroutine
instance
  (Monoid symbolSet, ExtractSymbolics symbolSet (m (Either (sus (Coroutine sus m a)) a))) =>
  ExtractSymbolics symbolSet (Coroutine sus m a)
  where
  extractSymbolics (Coroutine v) = extractSymbolics v

-- Sum
deriving via
  (Default (Sum f g a))
  instance
    (Monoid symbolSet, ExtractSymbolics symbolSet (f a), ExtractSymbolics symbolSet (g a)) =>
    ExtractSymbolics symbolSet (Sum f g a)

-- WriterT
instance
  (Monoid symbolSet, ExtractSymbolics symbolSet (m (a, s))) =>
    ExtractSymbolics symbolSet (WriterLazy.WriterT s m a) where
  extractSymbolics (WriterLazy.WriterT f) = extractSymbolics f

instance
  (Monoid symbolSet, ExtractSymbolics symbolSet (m (a, s))) =>
    ExtractSymbolics symbolSet (WriterStrict.WriterT s m a) where
  extractSymbolics (WriterStrict.WriterT f) = extractSymbolics f

-- Identity
instance (Monoid symbolSet, ExtractSymbolics symbolSet a) => ExtractSymbolics symbolSet (Identity a) where
  extractSymbolics (Identity a) = extractSymbolics a

-- IdentityT
instance (Monoid symbolSet, ExtractSymbolics symbolSet (m a)) => ExtractSymbolics symbolSet (IdentityT m a) where
  extractSymbolics (IdentityT a) = extractSymbolics a
