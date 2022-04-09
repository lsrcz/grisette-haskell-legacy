{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.ToSym
  ( ToSym (..),
  )
where

import Control.Monad.State.Lazy as StateLazy
import Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import Generics.Deriving
import Grisette.Data.Class.OrphanGeneric ()

-- | Convert a concrete value to symbolic value.
class ToSym a b where
  -- | Convert a concrete value to symbolic value.
  toSym :: a -> b

instance (Generic a, Generic b, ToSym' (Rep a) (Rep b)) => ToSym a (Default b) where
  toSym = Default . to . toSym' . from

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

-- Char
instance ToSym Char Char where
  toSym = id

-- Unit
instance ToSym () () where
  toSym = id

-- ByteString
instance ToSym B.ByteString B.ByteString where
  toSym = id

-- Either
deriving via (Default (Either e2 a2)) instance (ToSym e1 e2, ToSym a1 a2) => ToSym (Either e1 a1) (Either e2 a2)

-- Maybe
deriving via (Default (Maybe b)) instance ToSym a b => ToSym (Maybe a) (Maybe b)

-- List
deriving via (Default [b]) instance (ToSym a b) => ToSym [a] [b]

-- (,)
deriving via (Default (b1, b2)) instance (ToSym a1 b1, ToSym a2 b2) => ToSym (a1, a2) (b1, b2)

-- (,,)
deriving via (Default (b1, b2, b3)) instance (ToSym a1 b1, ToSym a2 b2, ToSym a3 b3) => ToSym (a1, a2, a3) (b1, b2, b3)

-- (,,,)
deriving via
  (Default (a2, b2, c2, d2))
  instance
    (ToSym a1 a2, ToSym b1 b2, ToSym c1 c2, ToSym d1 d2) => ToSym (a1, b1, c1, d1) (a2, b2, c2, d2)

-- (,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2))
  instance
    (ToSym a1 a2, ToSym b1 b2, ToSym c1 c2, ToSym d1 d2, ToSym e1 e2) =>
    ToSym (a1, b1, c1, d1, e1) (a2, b2, c2, d2, e2)

-- (,,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2, f2))
  instance
  (ToSym a1 a2, ToSym b1 b2, ToSym c1 c2, ToSym d1 d2, ToSym e1 e2, ToSym f1 f2) =>
  ToSym (a1, b1, c1, d1, e1, f1) (a2, b2, c2, d2, e2, f2)

-- (,,,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2, f2, g2))
  instance
  (ToSym a1 a2, ToSym b1 b2, ToSym c1 c2, ToSym d1 d2, ToSym e1 e2, ToSym f1 f2, ToSym g1 g2) =>
  ToSym (a1, b1, c1, d1, e1, f1, g1) (a2, b2, c2, d2, e2, f2, g2)

-- (,,,,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2, f2, g2, h2))
  instance
  (ToSym a1 a2, ToSym b1 b2, ToSym c1 c2, ToSym d1 d2, ToSym e1 e2, ToSym f1 f2, ToSym g1 g2, ToSym h1 h2) =>
  ToSym (a1, b1, c1, d1, e1, f1, g1, h1) (a2, b2, c2, d2, e2, f2, g2, h2)

-- function
instance (ToSym a b) => ToSym (v -> a) (v -> b) where
  toSym f = toSym . f

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

-- StateT
instance (ToSym (s1 -> m1 (a1, s1)) (s2 -> m2 (a2, s2))) => ToSym (StateLazy.StateT s1 m1 a1) (StateLazy.StateT s2 m2 a2) where
  toSym (StateLazy.StateT f1) = StateLazy.StateT $ toSym f1

instance (ToSym (s1 -> m1 (a1, s1)) (s2 -> m2 (a2, s2))) => ToSym (StateStrict.StateT s1 m1 a1) (StateStrict.StateT s2 m2 a2) where
  toSym (StateStrict.StateT f1) = StateStrict.StateT $ toSym f1

-- Sum
deriving via
  (Default (Sum f1 g1 a1))
  instance (ToSym (f a) (f1 a1), ToSym (g a) (g1 a1)) => ToSym (Sum f g a) (Sum f1 g1 a1)
