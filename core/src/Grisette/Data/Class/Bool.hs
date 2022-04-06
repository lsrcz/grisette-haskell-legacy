{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Bool
  ( SEq (..),
    SEq' (..),
    LogicalOp (..),
    SymBoolOp,
    ITEOp (..),
  )
where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Sum
import Generics.Deriving
import Grisette.Data.Class.PrimWrapper
import {-# SOURCE #-} Grisette.Data.Class.SimpleMergeable

-- | Auxiliary class for 'SEq' instance derivation
class (SymBoolOp bool) => SEq' bool f where
  -- | Auxiliary function for '(==~)' derivation
  (==~~) :: f a -> f a -> bool

  infix 4 ==~~

instance (SymBoolOp bool) => SEq' bool U1 where
  _ ==~~ _ = conc True

instance (SymBoolOp bool) => SEq' bool V1 where
  _ ==~~ _ = conc True

instance (SymBoolOp bool, SEq bool c) => SEq' bool (K1 i c) where
  (K1 a) ==~~ (K1 b) = a ==~ b

instance (SymBoolOp bool, SEq' bool a) => SEq' bool (M1 i c a) where
  (M1 a) ==~~ (M1 b) = a ==~~ b

instance (SymBoolOp bool, SEq' bool a, SEq' bool b) => SEq' bool (a :+: b) where
  (L1 a) ==~~ (L1 b) = a ==~~ b
  (R1 a) ==~~ (R1 b) = a ==~~ b
  _ ==~~ _ = conc False

instance (SymBoolOp bool, SEq' bool a, SEq' bool b) => SEq' bool (a :*: b) where
  (a1 :*: b1) ==~~ (a2 :*: b2) = (a1 ==~~ a2) &&~ (b1 ==~~ b2)

-- | Symbolic Equality. Note that we can't use Haskell's 'Eq' class since symbolic comparison won't necessarily return
-- a concrete 'Bool' value.
--
-- The @bool@ type is the symbolic boolean type to return.
class (SymBoolOp bool) => SEq bool a where
  (==~) :: a -> a -> bool
  a ==~ b = nots $ a /=~ b
  infix 4 ==~

  (/=~) :: a -> a -> bool
  a /=~ b = nots $ a ==~ b
  infix 4 /=~
  {-# MINIMAL (==~) | (/=~) #-}

instance (Generic a, SymBoolOp bool, SEq' bool (Rep a)) => SEq bool (Default a) where
  Default l ==~ Default r = from l ==~~ from r

-- | Logical operators for symbolic booleans. 
class LogicalOp b where
  (||~) :: b -> b -> b
  a ||~ b = nots $ nots a &&~ nots b
  infixr 2 ||~
  (&&~) :: b -> b -> b
  a &&~ b = nots $ nots a ||~ nots b
  infixr 3 &&~
  nots :: b -> b
  xors :: b -> b -> b
  a `xors` b = (a &&~ nots b) ||~ (nots a &&~ b)
  implies :: b -> b -> b
  a `implies` b = nots a ||~ b
  {-# MINIMAL (||~), nots | (&&~), nots #-}

instance LogicalOp Bool where
  (||~) = (||)
  (&&~) = (&&)
  nots = not

-- | ITE operator for symbolic primitives, including symbolic boolean, integer, etc.
class ITEOp b v where
  ites :: b -> v -> v -> v

-- | Aggregation for the operations on symbolic boolean types
class (SimpleMergeable b b, SEq b b, Eq b, LogicalOp b, PrimWrapper b Bool, ITEOp b b) => SymBoolOp b

-- Bool
deriving via (Default Bool) instance (SymBoolOp bool) => SEq bool Bool

-- Integer
instance (SymBoolOp bool) => SEq bool Integer where
  l ==~ r = conc $ l == r

-- Char
instance (SymBoolOp bool) => SEq bool Char where
  l ==~ r = conc $ l == r

-- List
deriving via (Default [a]) instance (SymBoolOp bool, SEq bool a) => SEq bool [a]

-- Maybe
deriving via (Default (Maybe a)) instance (SymBoolOp bool, SEq bool a) => SEq bool (Maybe a)

-- Either
deriving via (Default (Either e a)) instance (SymBoolOp bool, SEq bool e, SEq bool a) => SEq bool (Either e a)

-- ExceptT
instance (SymBoolOp bool, SEq bool (m (Either e a))) => SEq bool (ExceptT e m a) where
  (ExceptT a) ==~ (ExceptT b) = a ==~ b

-- MaybeT
instance (SymBoolOp bool, SEq bool (m (Maybe a))) => SEq bool (MaybeT m a) where
  (MaybeT a) ==~ (MaybeT b) = a ==~ b

-- ()
deriving via (Default ()) instance (SymBoolOp bool) => SEq bool ()

-- (,)
deriving via (Default (a, b)) instance (SymBoolOp bool, SEq bool a, SEq bool b) => SEq bool (a, b)

-- (,,)
deriving via (Default (a, b, c)) instance (SymBoolOp bool, SEq bool a, SEq bool b, SEq bool c) => SEq bool (a, b, c)

-- (,,,)
deriving via
  (Default (a, b, c, d))
  instance
    (SymBoolOp bool, SEq bool a, SEq bool b, SEq bool c, SEq bool d) =>
    SEq bool (a, b, c, d)

-- (,,,,)
deriving via
  (Default (a, b, c, d, e))
  instance
    (SymBoolOp bool, SEq bool a, SEq bool b, SEq bool c, SEq bool d, SEq bool e) =>
    SEq bool (a, b, c, d, e)

-- (,,,,,)
deriving via
  (Default (a, b, c, d, e, f))
  instance
    (SymBoolOp bool, SEq bool a, SEq bool b, SEq bool c, SEq bool d, SEq bool e, SEq bool f) =>
    SEq bool (a, b, c, d, e, f)

-- (,,,,,,)
deriving via
  (Default (a, b, c, d, e, f, g))
  instance
    (SymBoolOp bool, SEq bool a, SEq bool b, SEq bool c, SEq bool d, SEq bool e, SEq bool f, SEq bool g) =>
    SEq bool (a, b, c, d, e, f, g)

-- (,,,,,,,)
deriving via
  (Default (a, b, c, d, e, f, g, h))
  instance
    (SymBoolOp bool, SEq bool a, SEq bool b, SEq bool c, SEq bool d, SEq bool e, SEq bool f, SEq bool g, SEq bool h) =>
    SEq bool (a, b, c, d, e, f, g, h)

-- ByteString
instance (SymBoolOp bool) => SEq bool B.ByteString where
  l ==~ r = conc $ l == r

-- Sum
deriving via
  (Default (Sum f g a))
  instance
    (SymBoolOp bool, SEq bool (f a), SEq bool (g a)) => SEq bool (Sum f g a)
