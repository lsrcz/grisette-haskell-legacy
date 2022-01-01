{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.ToSym (ToSym (..)) where

import Control.Monad.Coroutine
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Generics.Deriving
import Grisette.Data.Class.OrphanGeneric ()
import qualified Data.ByteString as B
import Data.Functor.Sum

class ToSym a b where
  toSym :: a -> b
  default toSym :: (Generic a, Generic b, ToSym' (Rep a) (Rep b)) => a -> b
  toSym = to . toSym' . from

class ToSym' a b where
  toSym' :: a c -> b c

instance ToSym' U1 U1 where
  toSym' = id

instance (ToSym a b) => ToSym' (K1 i a) (K1 i b) where
  toSym' (K1 a) = K1 $ toSym a

instance (ToSym' a b) => ToSym' (M1 i c1 a) (M1 i c2 b) where
  toSym' (M1 a) = M1 $ toSym' a

instance (ToSym' a1 a2, ToSym' b1 b2) => ToSym' (a1 :+: b1) (a2 :+: b2) where
  toSym' (L1 a) = L1 $ toSym' a
  toSym' (R1 b) = R1 $ toSym' b

instance (ToSym' a1 a2, ToSym' b1 b2) => ToSym' (a1 :*: b1) (a2 :*: b2) where
  toSym' (a :*: b) = toSym' a :*: toSym' b

-- Bool
instance ToSym Bool Bool where
  toSym = id

-- Integer
instance ToSym Integer Integer where
  toSym = id

-- Unit
instance ToSym () () where
  toSym = id

-- ByteString
instance ToSym B.ByteString B.ByteString where
  toSym = id

-- Either
instance (ToSym e1 e2, ToSym a1 a2) => ToSym (Either e1 a1) (Either e2 a2)

-- Maybe
instance ToSym a b => ToSym (Maybe a) (Maybe b)

-- List
instance (ToSym a b) => ToSym [a] [b]

-- (,)
instance (ToSym a1 b1, ToSym a2 b2) => ToSym (a1, a2) (b1, b2)

-- (,,)
instance (ToSym a1 b1, ToSym a2 b2, ToSym a3 b3) => ToSym (a1, a2, a3) (b1, b2, b3)

-- function
instance (ToSym a b, ToSym c d) => ToSym (d -> a) (c -> b) where
  toSym f = toSym . f . toSym

-- MaybeT
instance
  (ToSym (m1 (Maybe a)) (m2 (Maybe b))) =>
  ToSym (MaybeT m1 a) (MaybeT m2 b)
  where
  toSym (MaybeT v) = MaybeT $ toSym v

-- ExceptT
instance
  (ToSym (m1 (Either e1 a)) (m2 (Either e2 b))) =>
  ToSym (ExceptT e1 m1 a) (ExceptT e2 m2 b)
  where
  toSym (ExceptT v) = ExceptT $ toSym v

-- Coroutine
instance
  (ToSym (m1 (Either (sus (Coroutine sus m1 a)) a)) (m2 (Either (sus (Coroutine sus m2 b)) b))) =>
  ToSym (Coroutine sus m1 a) (Coroutine sus m2 b)
  where
  toSym (Coroutine a) = Coroutine $ toSym a

-- StateT
instance (ToSym (s1 -> m1 (a1, s1)) (s2 -> m2 (a2, s2))) => ToSym (StateT s1 m1 a1) (StateT s2 m2 a2) where
  toSym (StateT f1) = StateT $ toSym f1

-- Sum
instance (ToSym (f a) (f1 a1), ToSym (g a) (g1 a1)) => ToSym (Sum f g a) (Sum f1 g1 a1)