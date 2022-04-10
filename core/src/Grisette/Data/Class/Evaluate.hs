{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.Class.Evaluate
  ( Evaluate (..),
    evaluateToCon,
  )
where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import Data.Maybe
import Generics.Deriving
import Generics.Deriving.Instances ()
import Grisette.Data.Class.ToCon

-- | Evaluating symbolic variables with some model.
--
-- Usually the model is created with the solver, rather than by hand.
class Evaluate model a where
  -- | Evaluate a symbolic variable with some model, possibly fill in values for the missing variables.
  --
  -- >>> let model = insert empty (TermSymbol (Proxy @Integer) (SimpleSymbol "a")) (1 :: Integer)
  -- >>> evaluate False model ([ssymb "a", ssymb "b"] :: [SymInteger])
  -- [1I,b]
  -- >>> evaluate True model ([ssymb "a", ssymb "b"] :: [SymInteger])
  -- [1I,0I]
  evaluate :: Bool -> model -> a -> a

instance (Generic a, Evaluate' model (Rep a)) => Evaluate model (Default a) where
  evaluate fillDefault model = Default . to . evaluate' fillDefault model . from . unDefault

class Evaluate' model a where
  evaluate' :: Bool -> model -> a c -> a c

instance Evaluate' model U1 where
  evaluate' _ _ = id

instance Evaluate model c => Evaluate' model (K1 i c) where
  evaluate' fillDefault model (K1 v) = K1 $ evaluate fillDefault model v

instance Evaluate' model a => Evaluate' model (M1 i c a) where
  evaluate' fillDefault model (M1 v) = M1 $ evaluate' fillDefault model v

instance (Evaluate' model a, Evaluate' model b) => Evaluate' model (a :+: b) where
  evaluate' fillDefault model (L1 l) = L1 $ evaluate' fillDefault model l
  evaluate' fillDefault model (R1 r) = R1 $ evaluate' fillDefault model r

instance (Evaluate' model a, Evaluate' model b) => Evaluate' model (a :*: b) where
  evaluate' fillDefault model (a :*: b) = evaluate' fillDefault model a :*: evaluate' fillDefault model b

-- | Evaluate a symbolic variable with some model, fill in values for the missing variables,
-- and transform to concrete ones
--
-- >>> let model = insert empty (TermSymbol (Proxy @Integer) (SimpleSymbol "a")) (1 :: Integer)
-- >>> evaluateToCon model ([ssymb "a", ssymb "b"] :: [SymInteger]) :: [Integer]
-- [1,0]
evaluateToCon :: (ToCon a b, Evaluate model a) => model -> a -> b
evaluateToCon model a = fromJust $ toCon $ evaluate True model a

-- instances

-- Bool
instance Evaluate model Bool where
  evaluate _ _ = id

-- Integer
instance Evaluate model Integer where
  evaluate _ _ = id

-- Char
instance Evaluate model Char where
  evaluate _ _ = id

-- ()
instance Evaluate model () where
  evaluate _ _ = id

-- ByteString
instance Evaluate model B.ByteString where
  evaluate _ _ = id

-- Either
deriving via (Default (Either a b)) instance (Evaluate model a, Evaluate model b) => Evaluate model (Either a b)

-- Maybe
deriving via (Default (Maybe a)) instance (Evaluate model a) => Evaluate model (Maybe a)

-- List
deriving via (Default [a]) instance (Evaluate model a) => Evaluate model [a]

-- (,)
deriving via (Default (a, b)) instance (Evaluate model a, Evaluate model b) => Evaluate model (a, b)

-- (,,)
deriving via (Default (a, b, c)) instance (Evaluate model a, Evaluate model b, Evaluate model c) => Evaluate model (a, b, c)

-- (,,,)
deriving via
  (Default (a, b, c, d))
  instance
    (Evaluate model a, Evaluate model b, Evaluate model c, Evaluate model d) => Evaluate model (a, b, c, d)

-- (,,,,)
deriving via
  (Default (a, b, c, d, e))
  instance
    (Evaluate model a, Evaluate model b, Evaluate model c, Evaluate model d, Evaluate model e) =>
    Evaluate model (a, b, c, d, e)

-- (,,,,,)
deriving via
  (Default (a, b, c, d, e, f))
  instance
    (Evaluate model a, Evaluate model b, Evaluate model c, Evaluate model d, Evaluate model e, Evaluate model f) =>
    Evaluate model (a, b, c, d, e, f)

-- (,,,,,,)
deriving via
  (Default (a, b, c, d, e, f, g))
  instance
    ( Evaluate model a,
      Evaluate model b,
      Evaluate model c,
      Evaluate model d,
      Evaluate model e,
      Evaluate model f,
      Evaluate model g
    ) =>
    Evaluate model (a, b, c, d, e, f, g)

-- (,,,,,,,)
deriving via
  (Default (a, b, c, d, e, f, g, h))
  instance
    ( Evaluate model a,
      Evaluate model b,
      Evaluate model c,
      Evaluate model d,
      Evaluate model e,
      Evaluate model f,
      Evaluate model g,
      Evaluate model h
    ) =>
    Evaluate model ((,,,,,,,) a b c d e f g h)

-- MaybeT
instance (Evaluate model (m (Maybe a))) => Evaluate model (MaybeT m a) where
  evaluate fillDefault model (MaybeT v) = MaybeT $ evaluate fillDefault model v

-- ExceptT
instance (Evaluate model (m (Either e a))) => Evaluate model (ExceptT e m a) where
  evaluate fillDefault model (ExceptT v) = ExceptT $ evaluate fillDefault model v

-- Sum
deriving via
  (Default (Sum f g a))
  instance
    (Evaluate model (f a), Evaluate model (g a)) => Evaluate model (Sum f g a)
