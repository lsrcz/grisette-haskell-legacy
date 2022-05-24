{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Mergeable
  ( MergeStrategy (..),
    Mergeable (..),
    Mergeable' (..),
    Mergeable1 (..),
    mergeStrategy1,
    Mergeable2 (..),
    mergeStrategy2,
    -- withMergeable,
    derivedMergeStrategy,
    wrapMergeStrategy,
    wrapMergeStrategy2,
    DynamicOrderedIdx (..),
    StrategyList (..),
    buildStrategyList,
    resolveStrategy,
    resolveStrategy',
  )
where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import qualified Data.ByteString as B
import Data.Functor.Classes
import Data.Functor.Sum
import Data.Int
import Data.Kind
import Data.Parameterized
import Data.Typeable
import qualified Data.Vector.Generic as VGeneric
import qualified Data.Vector.Generic.Sized as VSized
import Data.Word
import GHC.TypeLits
import Generics.Deriving
import Grisette.Data.Class.Bool
import Grisette.Data.Class.OrphanGeneric ()
import Unsafe.Coerce

-- | Helper type for combining arbitrary number of indices into one.
-- Useful when trying to write efficient merge strategy for lists / vectors.
data DynamicOrderedIdx where
  DynamicOrderedIdx :: forall idx. (Show idx, Ord idx, Typeable idx) => idx -> DynamicOrderedIdx

instance Eq DynamicOrderedIdx where
  (DynamicOrderedIdx (a :: a)) == (DynamicOrderedIdx (b :: b)) = case eqT @a @b of
    Just Refl -> a == b
    _ -> False

instance Ord DynamicOrderedIdx where
  compare (DynamicOrderedIdx (a :: a)) (DynamicOrderedIdx (b :: b)) = case eqT @a @b of
    Just Refl -> compare a b
    _ -> error "This Ord is incomplete"

instance Show DynamicOrderedIdx where
  show (DynamicOrderedIdx a) = show a

-- Resolves the indices and the terminal merge strategy for a value of some 'Mergeable' type.
resolveStrategy :: forall bool x. MergeStrategy bool x -> x -> ([DynamicOrderedIdx], MergeStrategy bool x)
resolveStrategy s x = resolveStrategy' x s

-- Resolves the indices and the terminal merge strategy for a value given a merge strategy for its type.
resolveStrategy' :: forall bool x. x -> MergeStrategy bool x -> ([DynamicOrderedIdx], MergeStrategy bool x)
resolveStrategy' x = go
  where
    go :: MergeStrategy bool x -> ([DynamicOrderedIdx], MergeStrategy bool x)
    go (OrderedStrategy idxFun subStrategy) = case go ss of
      (idxs, r) -> (DynamicOrderedIdx idx : idxs, r)
      where
        idx = idxFun x
        ss = subStrategy idx
    go s = ([], s)

-- | Merge strategy types.
--
-- A merge strategy encodes how to merge a __/subset/__ of the values of a given type.
--
-- The 'SimpleStrategy' merges values with a simple merge function.
-- For example,
--
--    (1) the symbolic boolean values can be directly merged with 'ites'.
--
--    (2) the set @{1}@, which is a subset of the values of the type @Integer@,
--        can be simply merged as the set contains only a single value.
--
--    (3) all the 'Just' values of the type @Maybe SymBool@ can be simply merged
--        by merging the wrapped symbolic boolean with ites.
--
-- The 'OrderedStrategy' merges values by first grouping the values with an indexing
-- function. Each group with be merged in a subtree with a sub-strategy for the index.
-- Grisette will use these information to generate efficient SMT formula.
-- For example,
--
--    (1) all the integers can be merged with 'OrderedStrategy' by indexing with identity map
--        and use the 'SimpleStrategy' shown before as the sub-strategies.
--
--    (2) all the @Maybe SymBool@ values can be merged with 'OrderedStrategy' by
--        indexing with 'Data.Maybe.isJust'.
--
-- The 'NoStrategy' does not perform any merging.
-- For example, we cannot merge functions that returns concrete lists.
--
-- Usually the user does not have to implement 'MergeStrategy' manually,
-- and the derived 'Mergeable' type class for ADTs is sufficient.
data MergeStrategy bool a where
  -- | Simple mergeable strategy.
  --
  -- For symbolic booleans, we can implement its merge strategy as follows:
  --
  -- > SimpleStrategy ites :: MergeStrategy SymBool SymBool
  SimpleStrategy ::
    -- | Merge function.
    (bool -> a -> a -> a) ->
    MergeStrategy bool a
  -- | Ordered mergeable strategy.
  --
  -- For Integers, we can implement its merge strategy as follows:
  --
  -- > OrderedStrategy id (\_ -> SimpleStrategy $ \_ t _ -> t)
  --
  -- For @Maybe SymBool@, we can implement its merge strategy as follows:
  --
  -- > OrderedStrategy
  -- >   (\case; Nothing -> False; Just _ -> True)
  -- >   (\idx ->
  -- >      if idx
  -- >        then SimpleStrategy $ \_ t _ -> t
  -- >        else SimpleStrategy $ \cond (Just l) (Just r) -> Just $ ites cond l r)
  OrderedStrategy ::
    (Ord idx, Typeable idx, Show idx) =>
    -- | Indexing function
    (a -> idx) ->
    -- | Sub-strategy function
    (idx -> MergeStrategy bool a) ->
    MergeStrategy bool a
  NoStrategy :: MergeStrategy bool a

-- | Useful utility function for building merge strategies manually.
--
-- For example, to build the merge strategy for the just branch of 'Maybe a',
-- one could write
--
-- > wrapMergeStrategy Just fromMaybe mergeStrategy :: MergeStrategy (Maybe a)
wrapMergeStrategy ::
  -- | The merge strategy to be wrapped
  MergeStrategy bool a ->
  -- | The wrap function
  (a -> b) ->
  -- | The unwrap function, which does not have to be defined for every value
  (b -> a) ->
  MergeStrategy bool b
wrapMergeStrategy (SimpleStrategy m) wrap unwrap =
  SimpleStrategy
    ( \cond ifTrue ifFalse ->
        wrap $ m cond (unwrap ifTrue) (unwrap ifFalse)
    )
wrapMergeStrategy (OrderedStrategy idxFun substrategy) wrap unwrap =
  OrderedStrategy
    (idxFun . unwrap)
    (\idx -> wrapMergeStrategy (substrategy idx) wrap unwrap)
wrapMergeStrategy NoStrategy _ _ = NoStrategy
{-# INLINE wrapMergeStrategy #-}

-- | Each type is associated with a root merge strategy given by 'mergeStrategy'.
-- The root merge strategy should be able to merge every value of the type.
-- Grisette will use the root merge strategy to merge the values of the type.
class Mergeable bool a where
  mergeStrategy :: MergeStrategy bool a

instance (Generic a, Mergeable' bool (Rep a)) => Mergeable bool (Default a) where
  mergeStrategy = unsafeCoerce (derivedMergeStrategy :: MergeStrategy bool a)
  {-# NOINLINE mergeStrategy #-}

-- | Generic derivation for the 'Mergeable' class.
derivedMergeStrategy :: (Generic a, Mergeable' bool (Rep a)) => MergeStrategy bool a
derivedMergeStrategy = wrapMergeStrategy mergeStrategy' to from
{-# INLINE derivedMergeStrategy #-}

-- | Lifting of the 'Mergeable' class to unary type constructors.
class Mergeable1 bool (u :: Type -> Type) where
  -- | Lift merge strategy through the type constructor.
  liftMergeStrategy :: MergeStrategy bool a -> MergeStrategy bool (u a)

-- | Lift the root merge strategy through the unary type constructor.
mergeStrategy1 :: (Mergeable bool a, Mergeable1 bool u) => MergeStrategy bool (u a)
mergeStrategy1 = liftMergeStrategy mergeStrategy

-- | Lifting of the 'Mergeable' class to binary type constructors.
class Mergeable2 bool (u :: Type -> Type -> Type) where
  liftMergeStrategy2 :: MergeStrategy bool a -> MergeStrategy bool b -> MergeStrategy bool (u a b)

-- | Lift the root merge strategy through the binary type constructor.
mergeStrategy2 :: (Mergeable bool a, Mergeable bool b, Mergeable2 bool u) => MergeStrategy bool (u a b)
mergeStrategy2 = liftMergeStrategy2 mergeStrategy mergeStrategy


instance (Generic1 u, Mergeable1' bool (Rep1 u)) => Mergeable1 bool (Default1 u) where
  liftMergeStrategy = unsafeCoerce (derivedLiftMergeStrategy :: MergeStrategy bool a -> MergeStrategy bool (u a))
  {-# NOINLINE liftMergeStrategy #-}

class Mergeable1' bool (u :: Type -> Type) where
  liftMergeStrategy' :: MergeStrategy bool a -> MergeStrategy bool (u a)

instance Mergeable1' bool U1 where
  liftMergeStrategy' _ = SimpleStrategy (\_ t _ -> t)

instance Mergeable1' bool V1 where
  liftMergeStrategy' _ = SimpleStrategy (\_ t _ -> t)

instance Mergeable1' bool Par1 where
  liftMergeStrategy' m = wrapMergeStrategy m Par1 unPar1

instance Mergeable1 bool f => Mergeable1' bool (Rec1 f) where
  liftMergeStrategy' m = wrapMergeStrategy (liftMergeStrategy m) Rec1 unRec1

instance Mergeable bool c => Mergeable1' bool (K1 i c) where
  liftMergeStrategy' _ = wrapMergeStrategy mergeStrategy K1 unK1

instance Mergeable1' bool a => Mergeable1' bool (M1 i c a) where
  liftMergeStrategy' m = wrapMergeStrategy (liftMergeStrategy' m) M1 unM1

instance (Mergeable1' bool a, Mergeable1' bool b) => Mergeable1' bool (a :+: b) where
  liftMergeStrategy' m =
    OrderedStrategy
      ( \case
          L1 _ -> False
          R1 _ -> True
      )
      ( \idx ->
          if not idx
            then wrapMergeStrategy (liftMergeStrategy' m) L1 (\(L1 v) -> v)
            else wrapMergeStrategy (liftMergeStrategy' m) R1 (\(R1 v) -> v)
      )

instance (Mergeable1' bool a, Mergeable1' bool b) => Mergeable1' bool (a :*: b) where
  liftMergeStrategy' m = wrapMergeStrategy2 (:*:) (\(a :*: b) -> (a, b)) (liftMergeStrategy' m) (liftMergeStrategy' m)

-- | Generic derivation for the 'Mergeable' class.
derivedLiftMergeStrategy :: (Generic1 u, Mergeable1' bool (Rep1 u)) => MergeStrategy bool a -> MergeStrategy bool (u a)
derivedLiftMergeStrategy m = wrapMergeStrategy (liftMergeStrategy' m) to1 from1

{-
-- | Resolves the 'Mergeable' constraint through a 'Mergeable1' type constructor.
withMergeable :: forall bool u a b. (Mergeable1 bool u, Mergeable bool a) => (Mergeable bool (u a) => b) -> b
withMergeable v = unCConst $ withMergeableT @bool @u @a @(CConst (Mergeable bool (u a)) b) $ CConst v
-}

-- | Auxiliary class for the generic derivation for the 'Mergeable' class.
class Mergeable' bool f where
  mergeStrategy' :: MergeStrategy bool (f a)

instance Mergeable' bool U1 where
  mergeStrategy' = SimpleStrategy (\_ t _ -> t)
  {-# INLINE mergeStrategy' #-}

instance Mergeable' bool V1 where
  mergeStrategy' = SimpleStrategy (\_ t _ -> t)
  {-# INLINE mergeStrategy' #-}

instance (Mergeable bool c) => Mergeable' bool (K1 i c) where
  mergeStrategy' = wrapMergeStrategy mergeStrategy K1 unK1
  {-# INLINE mergeStrategy' #-}

instance (Mergeable' bool a) => Mergeable' bool (M1 i c a) where
  mergeStrategy' = wrapMergeStrategy mergeStrategy' M1 unM1
  {-# INLINE mergeStrategy' #-}

instance (Mergeable' bool a, Mergeable' bool b) => Mergeable' bool (a :+: b) where
  mergeStrategy' =
    OrderedStrategy
      ( \case
          L1 _ -> False
          R1 _ -> True
      )
      ( \idx ->
          if not idx
            then wrapMergeStrategy mergeStrategy' L1 (\(L1 v) -> v)
            else wrapMergeStrategy mergeStrategy' R1 (\(R1 v) -> v)
      )
  {-# INLINE mergeStrategy' #-}

wrapMergeStrategy2 ::
  (a -> b -> r) ->
  (r -> (a, b)) ->
  MergeStrategy bool a ->
  MergeStrategy bool b ->
  MergeStrategy bool r
wrapMergeStrategy2 wrap unwrap strategy1 strategy2 =
  case (strategy1, strategy2) of
    (NoStrategy, _) -> NoStrategy
    (_, NoStrategy) -> NoStrategy
    (SimpleStrategy m1, SimpleStrategy m2) ->
      SimpleStrategy $ \cond t f -> case (unwrap t, unwrap f) of
        ((hdt, tlt), (hdf, tlf)) ->
          wrap (m1 cond hdt hdf) (m2 cond tlt tlf)
    (s1@(SimpleStrategy _), OrderedStrategy idxf subf) ->
      OrderedStrategy (idxf . snd . unwrap) (wrapMergeStrategy2 wrap unwrap s1 . subf)
    (OrderedStrategy idxf subf, s2) ->
      OrderedStrategy (idxf . fst . unwrap) (\idx -> wrapMergeStrategy2 wrap unwrap (subf idx) s2)
{-# INLINE wrapMergeStrategy2 #-}

instance (Mergeable' bool a, Mergeable' bool b) => Mergeable' bool (a :*: b) where
  mergeStrategy' = wrapMergeStrategy2 (:*:) (\(a :*: b) -> (a, b)) mergeStrategy' mergeStrategy'
  {-# INLINE mergeStrategy' #-}

-- instances

#define CONCRETE_ORD_MERGABLE(type) \
instance (SymBoolOp bool) => Mergeable bool type where \
  mergeStrategy = \
    let sub = SimpleStrategy $ \_ t _ -> t \
     in OrderedStrategy id $ const sub

CONCRETE_ORD_MERGABLE (Bool)
CONCRETE_ORD_MERGABLE (Integer)
CONCRETE_ORD_MERGABLE (Char)
CONCRETE_ORD_MERGABLE (Int)
CONCRETE_ORD_MERGABLE (Int8)
CONCRETE_ORD_MERGABLE (Int16)
CONCRETE_ORD_MERGABLE (Int32)
CONCRETE_ORD_MERGABLE (Int64)
CONCRETE_ORD_MERGABLE (Word)
CONCRETE_ORD_MERGABLE (Word8)
CONCRETE_ORD_MERGABLE (Word16)
CONCRETE_ORD_MERGABLE (Word32)
CONCRETE_ORD_MERGABLE (Word64)
CONCRETE_ORD_MERGABLE (B.ByteString)

-- ()
deriving via (Default ()) instance (SymBoolOp bool) => Mergeable bool ()

-- Either
deriving via (Default (Either e a)) instance (SymBoolOp bool, Mergeable bool e, Mergeable bool a) => Mergeable bool (Either e a)

deriving via (Default1 (Either e)) instance (SymBoolOp bool, Mergeable bool e) => Mergeable1 bool (Either e)

instance (SymBoolOp bool) => Mergeable2 bool Either where
  liftMergeStrategy2 m1 m2 =
    OrderedStrategy
      ( \case
          Left _ -> False
          Right _ -> True
      )
      ( \case
          False -> wrapMergeStrategy m1 Left (\(Left v) -> v)
          True -> wrapMergeStrategy m2 Right (\(Right v) -> v)
      )

-- Maybe
deriving via (Default (Maybe a)) instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (Maybe a)

deriving via (Default1 Maybe) instance (SymBoolOp bool) => Mergeable1 bool Maybe

-- | Helper type for building efficient merge strategy for list-like containers.
data StrategyList container where
  StrategyList ::
    forall bool a container.
    container [DynamicOrderedIdx] ->
    container (MergeStrategy bool a) ->
    StrategyList container

-- | Helper function for building efficient merge strategy for list-like containers.
buildStrategyList ::
  forall bool a container.
  (Functor container) =>
  MergeStrategy bool a ->
  container a ->
  StrategyList container
buildStrategyList s l = StrategyList idxs strategies
  where
    r = resolveStrategy @bool s <$> l
    idxs = fst <$> r
    strategies = snd <$> r

instance Eq1 container => Eq (StrategyList container) where
  (StrategyList idxs1 _) == (StrategyList idxs2 _) = eq1 idxs1 idxs2

instance Ord1 container => Ord (StrategyList container) where
  compare (StrategyList idxs1 _) (StrategyList idxs2 _) = compare1 idxs1 idxs2

instance Show1 container => Show (StrategyList container) where
  showsPrec i (StrategyList idxs1 _) = showsPrec1 i idxs1

-- List
instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool [a] where
  mergeStrategy = case mergeStrategy :: MergeStrategy bool a of
    SimpleStrategy m ->
      OrderedStrategy length $ \_ ->
        SimpleStrategy $ \cond -> zipWith (m cond)
    NoStrategy ->
      OrderedStrategy length $ const NoStrategy
    _ -> OrderedStrategy length $ \_ ->
      OrderedStrategy (buildStrategyList @bool mergeStrategy) $ \(StrategyList _ strategies) ->
        let s :: [MergeStrategy bool a] = unsafeCoerce strategies
            allSimple = all (\case SimpleStrategy _ -> True; _ -> False) s
         in if allSimple
              then SimpleStrategy $ \cond l r -> (\(SimpleStrategy f, l1, r1) -> f cond l1 r1) <$> zip3 s l r
              else NoStrategy

instance (SymBoolOp bool) => Mergeable1 bool [] where
  liftMergeStrategy (ms :: MergeStrategy bool a) = case ms of
    SimpleStrategy m ->
      OrderedStrategy length $ \_ ->
        SimpleStrategy $ \cond -> zipWith (m cond)
    NoStrategy ->
      OrderedStrategy length $ const NoStrategy
    _ -> OrderedStrategy length $ \_ ->
      OrderedStrategy (buildStrategyList @bool ms) $ \(StrategyList _ strategies) ->
        let s :: [MergeStrategy bool a] = unsafeCoerce strategies
            allSimple = all (\case SimpleStrategy _ -> True; _ -> False) s
         in if allSimple
              then SimpleStrategy $ \cond l r -> (\(SimpleStrategy f, l1, r1) -> f cond l1 r1) <$> zip3 s l r
              else NoStrategy

-- (,)
deriving via (Default (a, b)) instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable bool (a, b)

deriving via (Default1 ((,) a)) instance (SymBoolOp bool, Mergeable bool a) => Mergeable1 bool ((,) a)

instance SymBoolOp bool => Mergeable2 bool (,) where
  liftMergeStrategy2 m1 m2 = wrapMergeStrategy2 (,) id m1 m2

-- (,,)
deriving via
  (Default (a, b, c))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) => Mergeable bool (a, b, c)

deriving via
  (Default1 ((,,) a b))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable1 bool ((,,) a b)

-- (,,,)
deriving via
  (Default (a, b, c, d))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c, Mergeable bool d) =>
    Mergeable bool (a, b, c, d)

deriving via
  (Default1 ((,,,) a b c))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) =>
    Mergeable1 bool ((,,,) a b c)

-- (,,,,)
deriving via
  (Default (a, b, c, d, e))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c, Mergeable bool d, Mergeable bool e) =>
    Mergeable bool (a, b, c, d, e)

deriving via
  (Default1 ((,,,,) a b c d))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c, Mergeable bool d) =>
    Mergeable1 bool ((,,,,) a b c d)

-- (,,,,,)
deriving via
  (Default (a, b, c, d, e, f))
  instance
    ( SymBoolOp bool,
      Mergeable bool a,
      Mergeable bool b,
      Mergeable bool c,
      Mergeable bool d,
      Mergeable bool e,
      Mergeable bool f
    ) =>
    Mergeable bool (a, b, c, d, e, f)

deriving via
  (Default1 ((,,,,,) a b c d e))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c, Mergeable bool d, Mergeable bool e) =>
    Mergeable1 bool ((,,,,,) a b c d e)

-- (,,,,,,)
deriving via
  (Default (a, b, c, d, e, f, g))
  instance
    ( SymBoolOp bool,
      Mergeable bool a,
      Mergeable bool b,
      Mergeable bool c,
      Mergeable bool d,
      Mergeable bool e,
      Mergeable bool f,
      Mergeable bool g
    ) =>
    Mergeable bool (a, b, c, d, e, f, g)

deriving via
  (Default1 ((,,,,,,) a b c d e f))
  instance
    ( SymBoolOp bool,
      Mergeable bool a,
      Mergeable bool b,
      Mergeable bool c,
      Mergeable bool d,
      Mergeable bool e,
      Mergeable bool f
    ) =>
    Mergeable1 bool ((,,,,,,) a b c d e f)

-- (,,,,,,,)
deriving via
  (Default (a, b, c, d, e, f, g, h))
  instance
    ( SymBoolOp bool,
      Mergeable bool a,
      Mergeable bool b,
      Mergeable bool c,
      Mergeable bool d,
      Mergeable bool e,
      Mergeable bool f,
      Mergeable bool g,
      Mergeable bool h
    ) =>
    Mergeable bool (a, b, c, d, e, f, g, h)

deriving via
  (Default1 ((,,,,,,,) a b c d e f g))
  instance
    ( SymBoolOp bool,
      Mergeable bool a,
      Mergeable bool b,
      Mergeable bool c,
      Mergeable bool d,
      Mergeable bool e,
      Mergeable bool f,
      Mergeable bool g
    ) =>
    Mergeable1 bool ((,,,,,,,) a b c d e f g)

-- function
instance (SymBoolOp bool, Mergeable bool b) => Mergeable bool (a -> b) where
  mergeStrategy = case mergeStrategy @bool @b of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy

instance (SymBoolOp bool) => Mergeable1 bool ((->) a) where
  liftMergeStrategy ms = case ms of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy

-- MaybeT
instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) => Mergeable bool (MaybeT m a) where
  mergeStrategy = wrapMergeStrategy mergeStrategy1 MaybeT runMaybeT

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (MaybeT m) where
  liftMergeStrategy m = wrapMergeStrategy (liftMergeStrategy (liftMergeStrategy m)) MaybeT runMaybeT

-- ExceptT
instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ExceptT e m a)
  where
  mergeStrategy = wrapMergeStrategy mergeStrategy1 ExceptT runExceptT

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e) => Mergeable1 bool (ExceptT e m) where
  liftMergeStrategy m = wrapMergeStrategy (liftMergeStrategy (liftMergeStrategy m)) ExceptT runExceptT

-- state
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateLazy.StateT s m a)
  where
  mergeStrategy = wrapMergeStrategy (liftMergeStrategy mergeStrategy1) StateLazy.StateT StateLazy.runStateT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (StateLazy.StateT s m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy (liftMergeStrategy2 m mergeStrategy)))
      StateLazy.StateT
      StateLazy.runStateT

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateStrict.StateT s m a)
  where
  mergeStrategy =
    wrapMergeStrategy (liftMergeStrategy mergeStrategy1) StateStrict.StateT StateStrict.runStateT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (StateStrict.StateT s m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy (liftMergeStrategy2 m mergeStrategy)))
      StateStrict.StateT
      StateStrict.runStateT

-- writer
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (WriterLazy.WriterT s m a)
  where
  mergeStrategy = wrapMergeStrategy (liftMergeStrategy mergeStrategy1) WriterLazy.WriterT WriterLazy.runWriterT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (WriterLazy.WriterT s m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy2 m mergeStrategy))
      WriterLazy.WriterT
      WriterLazy.runWriterT

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (WriterStrict.WriterT s m a)
  where
  mergeStrategy = wrapMergeStrategy (liftMergeStrategy mergeStrategy1) WriterStrict.WriterT WriterStrict.runWriterT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (WriterStrict.WriterT s m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy2 m mergeStrategy))
      WriterStrict.WriterT
      WriterStrict.runWriterT

-- reader
instance
  (SymBoolOp bool, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (ReaderT s m a)
  where
  mergeStrategy = wrapMergeStrategy (liftMergeStrategy mergeStrategy1) ReaderT runReaderT

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (ReaderT s m) where
  liftMergeStrategy m =
    wrapMergeStrategy
      (liftMergeStrategy (liftMergeStrategy m))
      ReaderT
      runReaderT

-- Sum
instance
  (SymBoolOp bool, Mergeable1 bool l, Mergeable1 bool r, Mergeable bool x) =>
  Mergeable bool (Sum l r x)
  where
  mergeStrategy = OrderedStrategy (\case
    InL _ -> False
    InR _ -> True) (\case
      False -> wrapMergeStrategy mergeStrategy1 InL (\(InL v) -> v)
      True -> wrapMergeStrategy mergeStrategy1 InR (\(InR v) -> v))

instance (SymBoolOp bool, Mergeable1 bool l, Mergeable1 bool r) => Mergeable1 bool (Sum l r) where
  liftMergeStrategy m = OrderedStrategy (\case
    InL _ -> False
    InR _ -> True) (\case
      False -> wrapMergeStrategy (liftMergeStrategy m) InL (\(InL v) -> v)
      True -> wrapMergeStrategy (liftMergeStrategy m) InR (\(InR v) -> v))

-- Sized vector
instance
  ( SymBoolOp bool,
    Mergeable bool t,
    KnownNat m,
    VGeneric.Vector v t,
    VGeneric.Vector v (MergeStrategy bool t),
    Typeable v,
    Functor v,
    Eq1 v,
    Ord1 v,
    Show1 v,
    Foldable v
  ) =>
  Mergeable bool (VSized.Vector v m t)
  where
  mergeStrategy = case (isZeroOrGT1 (knownNat @m), mergeStrategy :: MergeStrategy bool t) of
    (Left Refl, _) -> SimpleStrategy $ \_ v _ -> v
    (Right LeqProof, SimpleStrategy m) -> SimpleStrategy $ \cond -> VSized.zipWith (m cond)
    (Right LeqProof, OrderedStrategy _ _) ->
      OrderedStrategy (buildStrategyList @bool mergeStrategy) $ \(StrategyList _ strategies) ->
        let s :: VSized.Vector v m (MergeStrategy bool t) = unsafeCoerce strategies
            allSimple = all (\case SimpleStrategy _ -> True; _ -> False) s
         in if allSimple
              then SimpleStrategy $ \cond l r ->
                VSized.zipWith3 (\(SimpleStrategy f) l1 r1 -> f cond l1 r1 :: t) s l r ::
                  VSized.Vector v m t
              else NoStrategy
    (Right LeqProof, NoStrategy) -> NoStrategy

-- Ordering
deriving via
  (Default Ordering)
  instance
    (SymBoolOp bool) => Mergeable bool Ordering

-- Generic
deriving via
  (Default (U1 x))
  instance
    (SymBoolOp bool) => Mergeable bool (U1 x)

deriving via
  (Default (V1 x))
  instance
    (SymBoolOp bool) => Mergeable bool (V1 x)

deriving via
  (Default (K1 i c x))
  instance
    (SymBoolOp bool, Mergeable bool c) => Mergeable bool (K1 i c x)

deriving via
  (Default (M1 i c a x))
  instance
    (SymBoolOp bool, Mergeable bool (a x)) => Mergeable bool (M1 i c a x)

deriving via
  (Default ((a :+: b) x))
  instance
    (SymBoolOp bool, Mergeable bool (a x), Mergeable bool (b x)) => Mergeable bool ((a :+: b) x)

deriving via
  (Default ((a :*: b) x))
  instance
    (SymBoolOp bool, Mergeable bool (a x), Mergeable bool (b x)) => Mergeable bool ((a :*: b) x)

-- Identity
instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (Identity a) where
  mergeStrategy = wrapMergeStrategy mergeStrategy Identity runIdentity

instance SymBoolOp bool => Mergeable1 bool Identity where
  liftMergeStrategy m = wrapMergeStrategy m Identity runIdentity

-- IdentityT
instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) => Mergeable bool (IdentityT m a) where
  mergeStrategy = wrapMergeStrategy mergeStrategy1 IdentityT runIdentityT

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (IdentityT m) where
  liftMergeStrategy m = wrapMergeStrategy (liftMergeStrategy m) IdentityT runIdentityT
