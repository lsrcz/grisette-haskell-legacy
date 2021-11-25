{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Grisette.Data.Class.ToCon where
import GHC.Generics
import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Monad.Coroutine

class ToCon a b where
  toCon :: a -> Maybe b
  default toCon :: (Generic a, Generic b, ToCon' (Rep a) (Rep b)) => a -> Maybe b
  toCon v = fmap to $ toCon' $ from v

class ToCon' a b where
  toCon' :: a c -> Maybe (b c)

instance ToCon' U1 U1 where
  toCon' = Just

instance ToCon a b => ToCon' (K1 i a) (K1 i b) where
  toCon' (K1 a) = K1 <$> toCon a

instance ToCon' a b => ToCon' (M1 i c a) (M1 i c b) where
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

-- Unit
instance ToCon () () where
  toCon = Just

-- Either
instance (ToCon e1 e2, ToCon a1 a2) => ToCon (Either e1 a1) (Either e2 a2)

-- Maybe
instance (ToCon a1 a2) => ToCon (Maybe a1) (Maybe a2)

-- List
instance (ToCon a b) => ToCon [a] [b]

-- (,)
instance (ToCon a1 a2, ToCon b1 b2) => ToCon (a1, b1) (a2, b2)

-- (,,)
instance (ToCon a1 a2, ToCon b1 b2, ToCon c1 c2) => ToCon (a1, b1, c1) (a2, b2, c2)

-- MaybeT
instance ToCon (m1 (Maybe a)) (m2 (Maybe b)) =>
  ToCon (MaybeT m1 a) (MaybeT m2 b) where
    toCon (MaybeT v) = MaybeT <$> toCon v

-- ExceptT
instance ToCon (m1 (Either e1 a)) (m2 (Either e2 b)) =>
  ToCon (ExceptT e1 m1 a) (ExceptT e2 m2 b) where
    toCon (ExceptT v) = ExceptT <$> toCon v

-- Coroutine
instance (ToCon (m1 (Either (sus (Coroutine sus m1 a)) a)) (m2 (Either (sus (Coroutine sus m2 b)) b))) =>
 ToCon (Coroutine sus m1 a) (Coroutine sus m2 b) where
   toCon (Coroutine a) = Coroutine <$> toCon a



