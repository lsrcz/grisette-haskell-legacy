{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}

module Grisette.Data.Class.Evaluate
  ( Evaluate (..),
    evaluateToCon,
  )
where

import Control.Monad.Except
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import Data.Maybe
import Generics.Deriving
import Generics.Deriving.Instances ()
import Grisette.Data.Class.ToCon
import Control.Monad.Identity
import Data.Int
import Data.Word

-- $setup
-- >>> import Grisette.Core
-- >>> import Grisette.IR.SymPrim
-- >>> import Data.Proxy

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

#define CONCRETE_EVALUATE(type) \
instance Evaluate model type where \
  evaluate _ _ = id

CONCRETE_EVALUATE(Bool)
CONCRETE_EVALUATE(Integer)
CONCRETE_EVALUATE(Char)
CONCRETE_EVALUATE(Int)
CONCRETE_EVALUATE(Int8)
CONCRETE_EVALUATE(Int16)
CONCRETE_EVALUATE(Int32)
CONCRETE_EVALUATE(Int64)
CONCRETE_EVALUATE(Word)
CONCRETE_EVALUATE(Word8)
CONCRETE_EVALUATE(Word16)
CONCRETE_EVALUATE(Word32)
CONCRETE_EVALUATE(Word64)
CONCRETE_EVALUATE(B.ByteString)

-- ()
instance Evaluate model () where
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

-- WriterT
instance Evaluate model (m (a, s)) => Evaluate model (WriterLazy.WriterT s m a) where
  evaluate fillDefault model (WriterLazy.WriterT v) = WriterLazy.WriterT $ evaluate fillDefault model v

instance Evaluate model (m (a, s)) => Evaluate model (WriterStrict.WriterT s m a) where
  evaluate fillDefault model (WriterStrict.WriterT v) = WriterStrict.WriterT $ evaluate fillDefault model v

-- Identity
instance Evaluate model a => Evaluate model (Identity a) where
  evaluate fillDefault model (Identity a) = Identity $ evaluate fillDefault model a

-- IdentityT
instance Evaluate model (m a) => Evaluate model (IdentityT m a) where
  evaluate fillDefault model (IdentityT a) = IdentityT $ evaluate fillDefault model a
