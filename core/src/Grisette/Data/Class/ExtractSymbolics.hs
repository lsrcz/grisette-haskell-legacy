{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.ExtractSymbolics (ExtractSymbolics (..)) where

import Control.Monad.Coroutine
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import GHC.Generics
import qualified Data.ByteString as B
import Data.Functor.Sum

class (Monoid symbolSet) => ExtractSymbolics symbolSet a where
  extractSymbolics :: a -> symbolSet
  default extractSymbolics :: (Generic a, ExtractSymbolics' symbolSet (Rep a)) => a -> symbolSet
  extractSymbolics = extractSymbolics' . from

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

-- ()
instance (Monoid symbolSet) => ExtractSymbolics symbolSet () where
  extractSymbolics _ = mempty

-- ByteString
instance (Monoid symbolSet) => ExtractSymbolics symbolSet B.ByteString where
  extractSymbolics _ = mempty

-- Either
instance
  (Monoid symbolSet, ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet b) =>
  ExtractSymbolics symbolSet (Either a b)

-- Maybe
instance (Monoid symbolSet, ExtractSymbolics symbolSet a) => ExtractSymbolics symbolSet (Maybe a)

-- List
instance (Monoid symbolSet, ExtractSymbolics symbolSet a) => ExtractSymbolics symbolSet [a]

-- (,)
instance
  (Monoid symbolSet, ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet b) =>
  ExtractSymbolics symbolSet (a, b)

-- (,,)
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
instance
  (Monoid symbolSet, ExtractSymbolics symbolSet (f a), ExtractSymbolics symbolSet (g a)) =>
  ExtractSymbolics symbolSet (Sum f g a)
