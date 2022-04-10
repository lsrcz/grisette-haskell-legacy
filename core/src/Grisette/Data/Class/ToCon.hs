{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.ToCon
  ( ToCon (..),
  )
where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import GHC.Generics
import Generics.Deriving
import Generics.Deriving.Instances ()

-- | Convert a symbolic value to concrete value if possible.
class ToCon a b where
  -- | Convert a symbolic value to concrete value if possible.
  -- If the symbolic value cannot be converted to concrete, the result will be 'Nothing'.
  --
  -- >>> toCon (ssymb "a" :: SymInteger) :: Maybe Integer
  -- Nothing
  --
  -- >>> toCon (conc 1 :: SymInteger) :: Maybe Integer
  -- Just 1
  --
  -- 'toCon' works on complex types too.
  --
  -- >>> toCon ([conc 1, conc 2] :: [SymInteger]) :: Maybe [Integer]
  -- Just [1,2]
  --
  -- >>> toCon ([conc 1, ssymb "a"] :: [SymInteger]) :: Maybe [Integer]
  -- Nothing
  toCon :: a -> Maybe b

instance (Generic a, Generic b, ToCon' (Rep a) (Rep b)) => ToCon a (Default b) where
  toCon v = fmap (Default . to) $ toCon' $ from v

class ToCon' a b where
  toCon' :: a c -> Maybe (b c)

instance ToCon' U1 U1 where
  toCon' = Just

instance ToCon a b => ToCon' (K1 i a) (K1 i b) where
  toCon' (K1 a) = K1 <$> toCon a

instance ToCon' a b => ToCon' (M1 i c1 a) (M1 i c2 b) where
  toCon' (M1 a) = M1 <$> toCon' a

instance (ToCon' a1 a2, ToCon' b1 b2) => ToCon' (a1 :+: b1) (a2 :+: b2) where
  toCon' (L1 a) = L1 <$> toCon' a
  toCon' (R1 a) = R1 <$> toCon' a

instance (ToCon' a1 a2, ToCon' b1 b2) => ToCon' (a1 :*: b1) (a2 :*: b2) where
  toCon' (a :*: b) = do
    ac <- toCon' a
    bc <- toCon' b
    return $ ac :*: bc

-- Bool
instance ToCon Bool Bool where
  toCon = Just

-- Integer
instance ToCon Integer Integer where
  toCon = Just

-- Char
instance ToCon Char Char where
  toCon = Just

-- Unit
instance ToCon () () where
  toCon = Just

-- ByteString
instance ToCon B.ByteString B.ByteString where
  toCon = Just

-- Either
deriving via (Default (Either e2 a2)) instance (ToCon e1 e2, ToCon a1 a2) => ToCon (Either e1 a1) (Either e2 a2)

-- Maybe
deriving via (Default (Maybe a2)) instance (ToCon a1 a2) => ToCon (Maybe a1) (Maybe a2)

-- List
deriving via (Default [b]) instance (ToCon a b) => ToCon [a] [b]

-- (,)
deriving via (Default (a2, b2)) instance (ToCon a1 a2, ToCon b1 b2) => ToCon (a1, b1) (a2, b2)

-- (,,)
deriving via (Default (a2, b2, c2)) instance (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2) => ToCon (a1, b1, c1) (a2, b2, c2)

-- (,,,)
deriving via
  (Default (a2, b2, c2, d2))
  instance
    (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2, ToCon d1 d2) => ToCon (a1, b1, c1, d1) (a2, b2, c2, d2)

-- (,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2))
  instance
    (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2, ToCon d1 d2, ToCon e1 e2) =>
    ToCon (a1, b1, c1, d1, e1) (a2, b2, c2, d2, e2)

-- (,,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2, f2))
  instance
    (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2, ToCon d1 d2, ToCon e1 e2, ToCon f1 f2) =>
    ToCon (a1, b1, c1, d1, e1, f1) (a2, b2, c2, d2, e2, f2)

-- (,,,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2, f2, g2))
  instance
    (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2, ToCon d1 d2, ToCon e1 e2, ToCon f1 f2, ToCon g1 g2) =>
    ToCon (a1, b1, c1, d1, e1, f1, g1) (a2, b2, c2, d2, e2, f2, g2)

-- (,,,,,,,)
deriving via
  (Default (a2, b2, c2, d2, e2, f2, g2, h2))
  instance
    (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2, ToCon d1 d2, ToCon e1 e2, ToCon f1 f2, ToCon g1 g2, ToCon h1 h2) =>
    ToCon (a1, b1, c1, d1, e1, f1, g1, h1) (a2, b2, c2, d2, e2, f2, g2, h2)

-- MaybeT
instance
  ToCon (m1 (Maybe a)) (m2 (Maybe b)) =>
  ToCon (MaybeT m1 a) (MaybeT m2 b)
  where
  toCon (MaybeT v) = MaybeT <$> toCon v

-- ExceptT
instance
  ToCon (m1 (Either e1 a)) (m2 (Either e2 b)) =>
  ToCon (ExceptT e1 m1 a) (ExceptT e2 m2 b)
  where
  toCon (ExceptT v) = ExceptT <$> toCon v

instance
  ToCon (m1 (Either e1 a)) (Either e2 b) =>
  ToCon (ExceptT e1 m1 a) (Either e2 b)
  where
  toCon (ExceptT v) = toCon v

-- Sum
deriving via
  (Default (Sum f1 g1 a1))
  instance
    (ToCon (f a) (f1 a1), ToCon (g a) (g1 a1)) => ToCon (Sum f g a) (Sum f1 g1 a1)
