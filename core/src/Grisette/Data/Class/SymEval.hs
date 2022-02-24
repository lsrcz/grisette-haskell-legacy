{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.SymEval
  ( SymEval (..),
    symevalToCon,
  )
where

import Control.Monad.Coroutine
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import Data.Maybe
import GHC.Generics
import Grisette.Data.Class.ToCon

class SymEval model a where
  symeval :: Bool -> model -> a -> a
  default symeval :: (Generic a, SymEval' model (Rep a)) => Bool -> model -> a -> a
  symeval fillDefault model = to . symeval' fillDefault model . from

class SymEval' model a where
  symeval' :: Bool -> model -> a c -> a c

instance SymEval' model U1 where
  symeval' _ _ = id

instance SymEval model c => SymEval' model (K1 i c) where
  symeval' fillDefault model (K1 v) = K1 $ symeval fillDefault model v

instance SymEval' model a => SymEval' model (M1 i c a) where
  symeval' fillDefault model (M1 v) = M1 $ symeval' fillDefault model v

instance (SymEval' model a, SymEval' model b) => SymEval' model (a :+: b) where
  symeval' fillDefault model (L1 l) = L1 $ symeval' fillDefault model l
  symeval' fillDefault model (R1 r) = R1 $ symeval' fillDefault model r

instance (SymEval' model a, SymEval' model b) => SymEval' model (a :*: b) where
  symeval' fillDefault model (a :*: b) = symeval' fillDefault model a :*: symeval' fillDefault model b

symevalToCon :: (ToCon a b, SymEval model a) => model -> a -> b
symevalToCon model a = fromJust $ toCon $ symeval True model a

-- instances

-- Bool
instance SymEval model Bool where
  symeval _ _ = id

-- Integer
instance SymEval model Integer where
  symeval _ _ = id

-- Char
instance SymEval model Char where
  symeval _ _ = id

-- ()
instance SymEval model () where
  symeval _ _ = id

-- ByteString
instance SymEval model B.ByteString where
  symeval _ _ = id

-- Either
instance (SymEval model a, SymEval model b) => SymEval model (Either a b)

-- Maybe
instance (SymEval model a) => SymEval model (Maybe a)

-- List
instance (SymEval model a) => SymEval model [a]

-- (,)
instance (SymEval model a, SymEval model b) => SymEval model (a, b)

-- (,,)
instance (SymEval model a, SymEval model b, SymEval model c) => SymEval model (a, b, c)

-- MaybeT
instance (SymEval model (m (Maybe a))) => SymEval model (MaybeT m a) where
  symeval fillDefault model (MaybeT v) = MaybeT $ symeval fillDefault model v

-- ExceptT
instance (SymEval model (m (Either e a))) => SymEval model (ExceptT e m a) where
  symeval fillDefault model (ExceptT v) = ExceptT $ symeval fillDefault model v

-- Coroutine
instance (SymEval model (m (Either (sus (Coroutine sus m a)) a))) => SymEval model (Coroutine sus m a) where
  symeval fillDefault model (Coroutine v) = Coroutine $ symeval fillDefault model v

-- Sum
instance (SymEval model (f a), SymEval model (g a)) => SymEval model (Sum f g a)