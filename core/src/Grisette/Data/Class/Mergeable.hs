{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.Class.Mergeable
  ( MergeStrategy (..),
    Mergeable (..),
    Mergeable' (..),
    Mergeable1 (..),
    withMergeable,
    derivedMergeStrategy,
    wrapMergeStrategy,
    DynamicOrderedIdx (..),
    StrategyList (..),
    buildStrategyList,
    resolveStrategy,
    resolveStrategy',
  )
where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Except
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import Data.Functor.Classes
import Data.Functor.Sum
import Data.Parameterized
import Data.Typeable
import qualified Data.Vector.Generic as VGeneric
import qualified Data.Vector.Generic.Sized as VSized
import GHC.TypeLits
import Generics.Deriving
import Grisette.Data.Class.Bool
import Grisette.Data.Class.OrphanGeneric ()
import Grisette.Data.Class.Utils.CConst
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
resolveStrategy :: forall bool x. (Mergeable bool x) => x -> ([DynamicOrderedIdx], MergeStrategy bool x)
resolveStrategy x = resolveStrategy' x mergeStrategy

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
class Mergeable1 bool (u :: * -> *) where
  -- | Resolves the 'Mergeable' constraint through the type constructor.
  --
  -- Usually you will not need to write this function manually.
  -- It should be available after you implement the 'Mergeable' class.
  withMergeableT :: forall a t. (Mergeable bool a) => (Mergeable bool (u a) => t a) -> t a
  default withMergeableT ::
    (forall b. Mergeable bool b => Mergeable bool (u b)) =>
    forall a t.
    (Mergeable bool a) =>
    (Mergeable bool (u a) => t a) ->
    t a
  withMergeableT v = v

-- | Resolves the 'Mergeable' constraint through a 'Mergeable1' type constructor.
withMergeable :: forall bool u a b. (Mergeable1 bool u, Mergeable bool a) => (Mergeable bool (u a) => b) -> b
withMergeable v = unCConst $ withMergeableT @bool @u @a @(CConst (Mergeable bool (u a)) b) $ CConst v

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

-- Bool
deriving via (Default Bool) instance (SymBoolOp bool) => Mergeable bool Bool

-- Integer
instance (SymBoolOp bool) => Mergeable bool Integer where
  mergeStrategy = OrderedStrategy id $ \_ -> SimpleStrategy $ \_ t _ -> t

-- Char
instance (SymBoolOp bool) => Mergeable bool Char where
  mergeStrategy = OrderedStrategy id $ \_ -> SimpleStrategy $ \_ t _ -> t

-- ()
deriving via (Default ()) instance (SymBoolOp bool) => Mergeable bool ()

-- ByteString
instance (SymBoolOp bool) => Mergeable bool B.ByteString where
  mergeStrategy = OrderedStrategy id $ \_ -> SimpleStrategy $ \_ t _ -> t

-- Either
deriving via (Default (Either e a)) instance (SymBoolOp bool, Mergeable bool e, Mergeable bool a) => Mergeable bool (Either e a)

instance (SymBoolOp bool, Mergeable bool e) => Mergeable1 bool (Either e)

-- Maybe
deriving via (Default (Maybe a)) instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (Maybe a)

instance (SymBoolOp bool) => Mergeable1 bool Maybe

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
  (Mergeable bool a, Functor container) =>
  container a ->
  StrategyList container
buildStrategyList l = StrategyList idxs strategies
  where
    r = resolveStrategy @bool <$> l
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
      OrderedStrategy (buildStrategyList @bool) $ \(StrategyList _ strategies) ->
        let s :: [MergeStrategy bool a] = unsafeCoerce strategies
            allSimple = all (\case SimpleStrategy _ -> True; _ -> False) s
         in if allSimple
              then SimpleStrategy $ \cond l r -> (\(SimpleStrategy f, l1, r1) -> f cond l1 r1) <$> zip3 s l r
              else NoStrategy

instance (SymBoolOp bool) => Mergeable1 bool []

-- (,)
deriving via (Default (a, b)) instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable bool (a, b)

instance (SymBoolOp bool, Mergeable bool a) => Mergeable1 bool ((,) a)

-- (,,)
deriving via
  (Default (a, b, c))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) => Mergeable bool (a, b, c)

instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable1 bool ((,,) a b)

-- (,,,)
deriving via
  (Default (a, b, c, d))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c, Mergeable bool d) =>
    Mergeable bool (a, b, c, d)

instance
  (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) =>
  Mergeable1 bool ((,,,) a b c)

-- (,,,,)
deriving via
  (Default (a, b, c, d, e))
  instance
    (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c, Mergeable bool d, Mergeable bool e) =>
    Mergeable bool (a, b, c, d, e)

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

instance (SymBoolOp bool) => Mergeable1 bool ((->) a)

-- MaybeT
instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a) => Mergeable bool (MaybeT m a) where
  mergeStrategy = withMergeable @bool @m @(Maybe a) $ wrapMergeStrategy mergeStrategy MaybeT runMaybeT

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (MaybeT m)

-- ExceptT
instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) =>
  Mergeable bool (ExceptT e m a)
  where
  mergeStrategy = withMergeable @bool @m @(Either e a) $ wrapMergeStrategy mergeStrategy ExceptT runExceptT

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Functor m) => Mergeable1 bool (ExceptT e m)

-- Coroutine
instance
  (SymBoolOp bool, Mergeable1 bool m, Mergeable bool a, Mergeable1 bool sus) =>
  Mergeable bool (Coroutine sus m a)
  where
  mergeStrategy =
    withMergeable @bool @sus @(Coroutine sus m a) $
      withMergeable @bool @m @(Either (sus (Coroutine sus m a)) a) $
        wrapMergeStrategy mergeStrategy Coroutine (\(Coroutine v) -> v)

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable1 bool sus) => Mergeable1 bool (Coroutine sus m)

deriving via
  (Default (Yield x y))
  instance
    (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Yield x y)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Yield x)

deriving via
  (Default (Await x y))
  instance
    (SymBoolOp bool, Mergeable bool x, Mergeable bool y) => Mergeable bool (Await x y)

instance (SymBoolOp bool, Mergeable bool x) => Mergeable1 bool (Await x)

deriving via
  (Default (Request req res x))
  instance
    (SymBoolOp bool, Mergeable bool req, Mergeable bool res, Mergeable bool x) =>
    Mergeable bool (Request req res x)

instance (SymBoolOp bool, Mergeable bool req, Mergeable bool res) => Mergeable1 bool (Request req res)

-- state
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateLazy.StateT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @(a, s) $
      withMergeable @bool @((->) s) @(m (a, s)) $
        wrapMergeStrategy mergeStrategy StateLazy.StateT StateLazy.runStateT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (StateLazy.StateT s m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (StateStrict.StateT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @(a, s) $
      withMergeable @bool @((->) s) @(m (a, s)) $
        wrapMergeStrategy mergeStrategy StateStrict.StateT StateStrict.runStateT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (StateStrict.StateT s m)

-- writer
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (WriterLazy.WriterT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @(a, s) $
      wrapMergeStrategy mergeStrategy WriterLazy.WriterT WriterLazy.runWriterT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (WriterLazy.WriterT s m)

instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (WriterStrict.WriterT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @(a, s) $
      wrapMergeStrategy mergeStrategy WriterStrict.WriterT WriterStrict.runWriterT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (WriterStrict.WriterT s m)

-- reader
instance
  (SymBoolOp bool, Mergeable bool s, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (ReaderT s m a)
  where
  mergeStrategy =
    withMergeable @bool @m @a $
      wrapMergeStrategy mergeStrategy ReaderT runReaderT

instance (SymBoolOp bool, Mergeable bool s, Mergeable1 bool m) => Mergeable1 bool (ReaderT s m)

-- Sum
instance
  (SymBoolOp bool, Mergeable1 bool l, Mergeable1 bool r, Mergeable bool x) =>
  Mergeable bool (Sum l r x)
  where
  mergeStrategy =
    withMergeable @bool @l @x $ withMergeable @bool @r @x $ derivedMergeStrategy

instance (SymBoolOp bool, Mergeable1 bool l, Mergeable1 bool r) => Mergeable1 bool (Sum l r)

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
      OrderedStrategy (buildStrategyList @bool) $ \(StrategyList _ strategies) ->
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
