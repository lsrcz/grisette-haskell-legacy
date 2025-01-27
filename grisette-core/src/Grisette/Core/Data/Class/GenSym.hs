{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Core.Data.Class.GenSym
  ( GenSymIndex (..),
    GenSymIdent,
    pattern GenSymIdent,
    pattern GenSymIdentWithInfo,
    name,
    nameWithInfo,
    MonadGenSymFresh (..),
    GenSymFreshT,
    GenSymFresh,
    runGenSymFreshT,
    runGenSymFresh,
    genSym,
    genSymSimple,
    GenSym (..),
    GenSymSimple (..),
    derivedNoSpecGenSymFresh,
    derivedNoSpecGenSymSimpleFresh,
    derivedSameShapeGenSymSimpleFresh,
    choose,
    simpleChoose,
    chooseU,
    ListSpec (..),
    SimpleListSpec (..),
    EnumGenBound (..),
    EnumGenUpperBound (..),
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Signatures
import Control.Monad.Trans.Maybe
import Data.Bifunctor
import qualified Data.ByteString as B
import Data.Hashable
import Data.Int
import Data.String
import Data.Typeable
import Data.Word
import Generics.Deriving hiding (index)
import Grisette.Core.Control.Monad.Union
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.SimpleMergeable
import Language.Haskell.TH.Syntax hiding (lift)

-- $setup
-- >>> import Grisette.Core
-- >>> import Grisette.IR.SymPrim
-- >>> :set -XOverloadedStrings
-- >>> :set -XTypeApplications

-- | Index type used for 'GenSym'.
--
-- To generate fresh variables, a monadic stateful context will be maintained.
-- Every time a new variable is generated, the index will be increased.
newtype GenSymIndex = GenSymIndex Int
  deriving (Show)
  deriving (Eq, Ord, Num) via Int

instance (SymBoolOp bool) => Mergeable bool GenSymIndex where
  mergingStrategy = SimpleStrategy $ \_ t f -> max t f

instance (SymBoolOp bool) => SimpleMergeable bool GenSymIndex where
  mrgIte _ t f = max t f

-- | Identifier type used for 'GenSym'
--
-- The constructor is hidden intentionally.
-- You can construct an identifier by:
--
--   * a raw name
--
--     >>> name "a"
--     a
--
--   * bundle the calling file location with the name to ensure global uniqueness
--
-- >>> $$(nameWithLoc "a") -- a sample result could be "a:<interactive>:18:4-18"
-- a:<interactive>:...
--
--   * bundle the calling file location with some user provided information
--
-- >>> nameWithInfo "a" (1 :: Int)
-- a:1
data GenSymIdent where
  GenSymIdent :: String -> GenSymIdent
  GenSymIdentWithInfo :: (Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> a -> GenSymIdent

instance Show GenSymIdent where
  show (GenSymIdent i) = i
  show (GenSymIdentWithInfo s i) = s ++ ":" ++ show i

instance IsString GenSymIdent where
  fromString = name

-- | Simple name identifier.
-- The same identifier refers to the same symbolic variable in the whole program.
--
-- The user need to ensure uniqueness by themselves if they need to.
name :: String -> GenSymIdent
name = GenSymIdent

-- | Identifier with extra information.
-- The same name with the same information
-- refers to the same symbolic variable in the whole program.
--
-- The user need to ensure uniqueness by themselves if they need to.
nameWithInfo :: forall a. (Typeable a, Ord a, Lift a, NFData a, Show a, Hashable a) => String -> a -> GenSymIdent
nameWithInfo = GenSymIdentWithInfo

class Monad m => MonadGenSymFresh m where
  nextGenSymIndex :: m GenSymIndex
  getGenSymIdent :: m GenSymIdent

-- | A symbolic generation monad transformer.
-- It is a reader monad transformer for identifiers and
-- a state monad transformer for indices.
--
-- Each time a fresh symbolic variable is generated, the index should be increased.
newtype GenSymFreshT m a = GenSymFreshT {runGenSymFreshT' :: GenSymIdent -> GenSymIndex -> m (a, GenSymIndex)}

instance
  (SymBoolOp bool, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (GenSymFreshT m a)
  where
  mergingStrategy =
    wrapStrategy (liftMergingStrategy (liftMergingStrategy mergingStrategy1)) GenSymFreshT runGenSymFreshT'

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (GenSymFreshT m) where
  liftMergingStrategy m =
    wrapStrategy
      (liftMergingStrategy (liftMergingStrategy (liftMergingStrategy (liftMergingStrategy2 m mergingStrategy))))
      GenSymFreshT
      runGenSymFreshT'

instance
  (SymBoolOp bool, UnionLike bool m, Mergeable bool a) =>
  SimpleMergeable bool (GenSymFreshT m a)
  where
  mrgIte = mrgIf

instance
  (SymBoolOp bool, UnionLike bool m) =>
  SimpleMergeable1 bool (GenSymFreshT m)
  where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance
  (SymBoolOp bool, UnionLike bool m) =>
  UnionLike bool (GenSymFreshT m)
  where
  mergeWithStrategy s (GenSymFreshT f) =
    GenSymFreshT $ \ident index -> mergeWithStrategy (liftMergingStrategy2 s mergingStrategy) $ f ident index
  mrgIfWithStrategy s cond (GenSymFreshT t) (GenSymFreshT f) =
    GenSymFreshT $ \ident index -> mrgIfWithStrategy (liftMergingStrategy2 s mergingStrategy) cond (t ident index) (f ident index)
  single x = GenSymFreshT $ \_ i -> single (x, i)
  unionIf cond (GenSymFreshT t) (GenSymFreshT f) =
    GenSymFreshT $ \ident index -> unionIf cond (t ident index) (f ident index)

-- | Run the symbolic generation with the given identifier and 0 as the initial index.
runGenSymFreshT :: (Monad m) => GenSymFreshT m a -> GenSymIdent -> m a
runGenSymFreshT m ident = fst <$> runGenSymFreshT' m ident (GenSymIndex 0)

instance (Functor f) => Functor (GenSymFreshT f) where
  fmap f (GenSymFreshT s) = GenSymFreshT $ \ident idx -> first f <$> s ident idx

instance (Applicative m, Monad m) => Applicative (GenSymFreshT m) where
  pure a = GenSymFreshT $ \_ idx -> pure (a, idx)
  GenSymFreshT fs <*> GenSymFreshT as = GenSymFreshT $ \ident idx -> do
    (f, idx') <- fs ident idx
    (a, idx'') <- as ident idx'
    return (f a, idx'')

instance (Monad m) => Monad (GenSymFreshT m) where
  (GenSymFreshT s) >>= f = GenSymFreshT $ \ident idx -> do
    (a, idx') <- s ident idx
    runGenSymFreshT' (f a) ident idx'

instance MonadTrans GenSymFreshT where
  lift x = GenSymFreshT $ \_ index -> (,index) <$> x

liftGenSymFreshTCache :: (Functor m) => Catch e m (a, GenSymIndex) -> Catch e (GenSymFreshT m) a
liftGenSymFreshTCache catchE (GenSymFreshT m) h =
  GenSymFreshT $ \ident index -> m ident index `catchE` \e -> runGenSymFreshT' (h e) ident index

instance (MonadError e m) => MonadError e (GenSymFreshT m) where
  throwError = lift . throwError
  catchError = liftGenSymFreshTCache catchError

-- | 'GenSymFreshT' specialized with Identity.
type GenSymFresh = GenSymFreshT Identity

-- | Run the symbolic generation with the given identifier and 0 as the initial index.
runGenSymFresh :: GenSymFresh a -> GenSymIdent -> a
runGenSymFresh m ident = runIdentity $ runGenSymFreshT m ident

instance Monad m => MonadGenSymFresh (GenSymFreshT m) where
  nextGenSymIndex = GenSymFreshT $ \_ idx -> return (idx, idx + 1)
  getGenSymIdent = GenSymFreshT $ curry return

{-
instance (Monad m) => MonadState GenSymIndex (GenSymFreshT m) where
  state f = GenSymFreshT $ \_ idx -> return $ f idx
  put newidx = GenSymFreshT $ \_ _ -> return ((), newidx)
  get = GenSymFreshT $ \_ idx -> return (idx, idx)

instance (Monad m) => MonadReader GenSymIdent (GenSymFreshT m) where
  ask = GenSymFreshT $ curry return
  local f (GenSymFreshT s) = GenSymFreshT $ \ident idx -> s (f ident) idx
  reader f = GenSymFreshT $ \r s -> return (f r, s)
  -}

-- | Class of types in which symbolic values can be generated with respect to some specification.
--
-- The result will be wrapped in a union-like monad.
-- This ensures that we can generate those types with complex merging rules.
--
-- The uniqueness with be managed with the a monadic context. 'GenSymFresh' and 'GenSymFreshT' can be useful.
class (SymBoolOp bool, Mergeable bool a) => GenSym bool spec a where
  -- | Generate a symbolic value given some specification. The uniqueness is ensured.
  --
  -- The following example generates a symbolic boolean. No specification is needed.
  --
  -- >>> runGenSymFresh (genSymFresh ()) "a" :: UnionM SymBool
  -- UMrg (Single a@0)
  --
  -- The following example generates booleans, which cannot be merged into a single value with type 'Bool'.
  -- No specification is needed.
  --
  -- >>> runGenSymFresh (genSymFresh ()) "a" :: UnionM Bool
  -- UMrg (If a@0 (Single False) (Single True))
  --
  -- The following example generates @Maybe Bool@s.
  -- There are more than one symbolic primitives introduced, and their uniqueness is ensured.
  -- No specification is needed.
  --
  -- >>> runGenSymFresh (genSymFresh ()) "a" :: UnionM (Maybe Bool)
  -- UMrg (If a@0 (Single Nothing) (If a@1 (Single (Just False)) (Single (Just True))))
  --
  -- The following example generates lists of symbolic booleans with length 1 to 2.
  --
  -- >>> runGenSymFresh (genSymFresh (ListSpec 1 2 ())) "a" :: UnionM [SymBool]
  -- UMrg (If a@2 (Single [a@1]) (Single [a@0,a@1]))
  --
  -- When multiple symbolic variables are generated, the uniqueness can be ensured.
  --
  -- >>> runGenSymFresh (do; a <- genSymFresh (); b <- genSymFresh (); return (a, b)) "a" :: (UnionM SymBool, UnionM SymBool)
  -- (UMrg (Single a@0),UMrg (Single a@1))
  --
  -- N.B.: the examples are not executable solely with @grisette-core@ package, and need support from @grisette-symprim@ package.
  genSymFresh ::
    ( MonadGenSymFresh m,
      MonadUnion bool u
    ) =>
    spec ->
    m (u a)
  default genSymFresh ::
    (GenSymSimple spec a) =>
    ( MonadGenSymFresh m,
      MonadUnion bool u
    ) =>
    spec ->
    m (u a)
  genSymFresh spec = mrgSingle <$> genSymSimpleFresh spec

-- | Generate a symbolic variable wrapped in a Union without the monadic context.
-- The uniqueness need to be ensured by the uniqueness of the provided identifier.
genSym :: (GenSym bool spec a, MonadUnion bool u) => spec -> GenSymIdent -> u a
genSym = runGenSymFresh . genSymFresh

-- | Class of types in which symbolic values can be generated with respect to some specification.
--
-- The result will __/not/__ be wrapped in a union-like monad.
--
-- The uniqueness with be managed with the a monadic context. 'GenSymFresh' and 'GenSymFreshT' can be useful.
class GenSymSimple spec a where
  -- | Generate a symbolic value given some specification. The uniqueness is ensured.
  --
  -- The following example generates a symbolic boolean. No specification is needed.
  --
  -- >>> runGenSymFresh (genSymSimpleFresh ()) "a" :: SymBool
  -- a@0
  --
  -- The example shows that why the system cannot infer the symbolic boolean type.
  --
  -- >>> runGenSymFresh (genSymSimpleFresh ()) "a" :: ()
  -- ()
  --
  -- The following code generates list of symbolic boolean with length 2.
  -- As the length is fixed, we don't have to wrap the result in unions.
  --
  -- >>> runGenSymFresh (genSymSimpleFresh (SimpleListSpec 2 ())) "a" :: [SymBool]
  -- [a@0,a@1]
  --
  -- N.B.: the examples are not executable solely with @grisette-core@ package, and need support from @grisette-symprim@ package.
  genSymSimpleFresh ::
    ( MonadGenSymFresh m
    ) =>
    spec ->
    m a

-- | Generate a simple symbolic variable wrapped in a Union without the monadic context.
-- The uniqueness need to be ensured by the uniqueness of the provided identifier.
genSymSimple :: forall spec a. (GenSymSimple spec a) => spec -> GenSymIdent -> a
genSymSimple = runGenSymFresh . genSymSimpleFresh

class GenSymNoSpec bool a where
  genSymFreshNoSpec ::
    ( MonadGenSymFresh m,
      MonadUnion bool u
    ) =>
    m (u (a c))

instance (SymBoolOp bool) => GenSymNoSpec bool U1 where
  genSymFreshNoSpec = return $ mrgSingle U1

instance (SymBoolOp bool, GenSym bool () c) => GenSymNoSpec bool (K1 i c) where
  genSymFreshNoSpec = fmap K1 <$> genSymFresh ()

instance (SymBoolOp bool, GenSymNoSpec bool a) => GenSymNoSpec bool (M1 i c a) where
  genSymFreshNoSpec = fmap M1 <$> genSymFreshNoSpec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSymNoSpec bool a,
    GenSymNoSpec bool b,
    forall x. Mergeable bool (a x),
    forall x. Mergeable bool (b x)
  ) =>
  GenSymNoSpec bool (a :+: b)
  where
  genSymFreshNoSpec ::
    forall m u c.
    ( MonadGenSymFresh m,
      MonadUnion bool u
    ) =>
    m (u ((a :+: b) c))
  genSymFreshNoSpec = do
    cond :: bool <- genSymSimpleFresh ()
    l :: u (a c) <- genSymFreshNoSpec
    r :: u (b c) <- genSymFreshNoSpec
    return $ mrgIf cond (fmap L1 l) (fmap R1 r)

instance
  (SymBoolOp bool, GenSymSimple () bool, GenSymNoSpec bool a, GenSymNoSpec bool b) =>
  GenSymNoSpec bool (a :*: b)
  where
  genSymFreshNoSpec ::
    forall m u c.
    ( MonadGenSymFresh m,
      MonadUnion bool u
    ) =>
    m (u ((a :*: b) c))
  genSymFreshNoSpec = do
    l :: u (a c) <- genSymFreshNoSpec
    r :: u (b c) <- genSymFreshNoSpec
    return $ do
      l1 <- l
      r1 <- r
      return $ l1 :*: r1

-- | We cannot provide DerivingVia style derivation for 'GenSym'.
--
-- This 'genSymFresh' implementation is for the types that does not need any specification.
-- It will generate product types by generating each fields with '()' as specification,
-- and generate all possible values for a sum type.
--
-- N.B. Never use on recursive types
derivedNoSpecGenSymFresh ::
  forall bool a m u.
  ( Generic a,
    SymBoolOp bool,
    GenSymNoSpec bool (Rep a),
    Mergeable bool a,
    MonadGenSymFresh m,
    MonadUnion bool u
  ) =>
  () ->
  m (u a)
derivedNoSpecGenSymFresh _ = merge . fmap to <$> genSymFreshNoSpec

class GenSymSimpleNoSpec a where
  genSymSimpleFreshNoSpec :: (MonadGenSymFresh m) => m (a c)

instance GenSymSimpleNoSpec U1 where
  genSymSimpleFreshNoSpec = return U1

instance (GenSymSimple () c) => GenSymSimpleNoSpec (K1 i c) where
  genSymSimpleFreshNoSpec = K1 <$> genSymSimpleFresh ()

instance (GenSymSimpleNoSpec a) => GenSymSimpleNoSpec (M1 i c a) where
  genSymSimpleFreshNoSpec = M1 <$> genSymSimpleFreshNoSpec

instance
  (GenSymSimpleNoSpec a, GenSymSimpleNoSpec b) =>
  GenSymSimpleNoSpec (a :*: b)
  where
  genSymSimpleFreshNoSpec = do
    l :: a c <- genSymSimpleFreshNoSpec
    r :: b c <- genSymSimpleFreshNoSpec
    return $ l :*: r

-- | We cannot provide DerivingVia style derivation for 'GenSymSimple'.
--
-- This 'genSymSimpleFresh' implementation is for the types that does not need any specification.
-- It will generate product types by generating each fields with '()' as specification.
-- It will not work on sum types.
--
-- N.B. Never use on recursive types
derivedNoSpecGenSymSimpleFresh ::
  forall a m.
  ( Generic a,
    GenSymSimpleNoSpec (Rep a),
    MonadGenSymFresh m
  ) =>
  () ->
  m a
derivedNoSpecGenSymSimpleFresh _ = to <$> genSymSimpleFreshNoSpec

class GenSymSameShape a where
  genSymSameShapeFresh ::
    ( MonadGenSymFresh m
    ) =>
    a c ->
    m (a c)

instance GenSymSameShape U1 where
  genSymSameShapeFresh _ = return U1

instance (GenSymSimple c c) => GenSymSameShape (K1 i c) where
  genSymSameShapeFresh (K1 c) = K1 <$> genSymSimpleFresh c

instance (GenSymSameShape a) => GenSymSameShape (M1 i c a) where
  genSymSameShapeFresh (M1 a) = M1 <$> genSymSameShapeFresh a

instance
  (GenSymSameShape a, GenSymSameShape b) =>
  GenSymSameShape (a :+: b)
  where
  genSymSameShapeFresh (L1 a) = L1 <$> genSymSameShapeFresh a
  genSymSameShapeFresh (R1 a) = R1 <$> genSymSameShapeFresh a

instance
  (GenSymSameShape a, GenSymSameShape b) =>
  GenSymSameShape (a :*: b)
  where
  genSymSameShapeFresh (a :*: b) = do
    l :: a c <- genSymSameShapeFresh a
    r :: b c <- genSymSameShapeFresh b
    return $ l :*: r

-- | We cannot provide DerivingVia style derivation for 'GenSymSimple'.
--
-- This 'genSymSimpleFresh' implementation is for the types that can be generated with a reference value of the same type.
--
-- For sum types, it will generate the result with the same data constructor.
-- For product types, it will generate the result by generating each field with the corresponding reference value.
--
-- N.B. Can be used on recursive types
derivedSameShapeGenSymSimpleFresh ::
  forall a m.
  ( Generic a,
    GenSymSameShape (Rep a),
    MonadGenSymFresh m
  ) =>
  a ->
  m a
derivedSameShapeGenSymSimpleFresh a = to <$> genSymSameShapeFresh (from a)

-- | Symbolically chooses one of the provided values.
-- The procedure creates @n - 1@ fresh symbolic boolean variables every time it is evaluated, and use
-- these variables to conditionally select one of the @n@ provided expressions.
--
-- The result will be wrapped in a union-like monad, and also a monad maintaining the 'GenSym' context.
--
-- >>> runGenSymFresh (choose [1,2,3]) "a" :: UnionM Integer
-- UMrg (If a@0 (Single 1) (If a@1 (Single 2) (Single 3)))
choose ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    GenSymSimple () bool,
    MonadGenSymFresh m,
    MonadUnion bool u
  ) =>
  [a] ->
  m (u a)
choose [x] = return $ mrgSingle x
choose (r : rs) = do
  b <- genSymSimpleFresh ()
  res <- choose rs
  return $ mrgIf b (mrgSingle r) res
choose [] = error "choose expects at least one value"

-- | Symbolically chooses one of the provided values.
-- The procedure creates @n - 1@ fresh symbolic boolean variables every time it is evaluated, and use
-- these variables to conditionally select one of the @n@ provided expressions.
--
-- The result will __/not/__ be wrapped in a union-like monad, but will be wrapped in a monad maintaining the 'GenSym' context.
-- Similar to 'genSymSimpleFresh', you need to tell the system what symbolic boolean type to use.
--
-- >>> runGenSymFresh (simpleChoose (Proxy @SymBool) [ssymb "b", ssymb "c", ssymb "d"]) "a" :: SymInteger
-- (ite a@0 b (ite a@1 c d))
simpleChoose ::
  forall proxy bool a m.
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    GenSymSimple () bool,
    MonadGenSymFresh m
  ) =>
  proxy bool ->
  [a] ->
  m a
simpleChoose _ [x] = return x
simpleChoose proxy (r : rs) = do
  b :: bool <- genSymSimpleFresh ()
  res <- simpleChoose proxy rs
  return $ mrgIte b r res
simpleChoose _ [] = error "simpleChoose expects at least one value"

-- | Symbolically chooses one of the provided values wrapped in union-like monads.
-- The procedure creates @n - 1@ fresh symbolic boolean variables every time it is evaluated, and use
-- these variables to conditionally select one of the @n@ provided expressions.
--
-- The result will be wrapped in a union-like monad, and also a monad maintaining the 'GenSym' context.
--
-- >>> let a = runGenSymFresh (choose [1, 2]) "a" :: UnionM Integer
-- >>> let b = runGenSymFresh (choose [2, 3]) "b" :: UnionM Integer
-- >>> runGenSymFresh (chooseU [a, b]) "c" :: UnionM Integer
-- UMrg (If (&& c@0 a@0) (Single 1) (If (|| c@0 b@0) (Single 2) (Single 3)))
chooseU ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    GenSymSimple () bool,
    MonadGenSymFresh m,
    MonadUnion bool u
  ) =>
  [u a] ->
  m (u a)
chooseU [x] = return x
chooseU (r : rs) = do
  b <- genSymSimpleFresh ()
  res <- chooseU rs
  return $ mrgIf b r res
chooseU [] = error "chooseU expects at least one value"

#define CONCRETE_GENSYM_SAMESHAPE(type) \
instance (SymBoolOp bool, GenSymSimple () bool) => GenSym bool type type where \
  genSymFresh v = return $ mrgSingle v;
#define CONCRETE_GENSYM_SIMPLE_SAMESHAPE(type) \
instance GenSymSimple type type where \
  genSymSimpleFresh v = return v

CONCRETE_GENSYM_SAMESHAPE (Bool)
CONCRETE_GENSYM_SAMESHAPE (Integer)
CONCRETE_GENSYM_SAMESHAPE (Char)
CONCRETE_GENSYM_SAMESHAPE (Int)
CONCRETE_GENSYM_SAMESHAPE (Int8)
CONCRETE_GENSYM_SAMESHAPE (Int16)
CONCRETE_GENSYM_SAMESHAPE (Int32)
CONCRETE_GENSYM_SAMESHAPE (Int64)
CONCRETE_GENSYM_SAMESHAPE (Word)
CONCRETE_GENSYM_SAMESHAPE (Word8)
CONCRETE_GENSYM_SAMESHAPE (Word16)
CONCRETE_GENSYM_SAMESHAPE (Word32)
CONCRETE_GENSYM_SAMESHAPE (Word64)
CONCRETE_GENSYM_SAMESHAPE (B.ByteString)

CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Bool)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Integer)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Char)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Int)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Int8)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Int16)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Int32)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Int64)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Word)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Word8)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Word16)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Word32)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (Word64)
CONCRETE_GENSYM_SIMPLE_SAMESHAPE (B.ByteString)

-- Bool
instance (SymBoolOp bool, GenSymSimple () bool) => GenSym bool () Bool where
  genSymFresh = derivedNoSpecGenSymFresh

-- Enums

-- | Specification for enum values with upper bound (exclusive). The result would chosen from [0 .. upperbound].
--
-- >>> runGenSymFresh (genSymFresh (EnumGenUpperBound @Integer 4)) "c" :: UnionM Integer
-- UMrg (If c@0 (Single 0) (If c@1 (Single 1) (If c@2 (Single 2) (Single 3))))
newtype EnumGenUpperBound a = EnumGenUpperBound a

instance (SymBoolOp bool, GenSymSimple () bool, Enum v, Mergeable bool v) => GenSym bool (EnumGenUpperBound v) v where
  genSymFresh (EnumGenUpperBound u) = choose (toEnum <$> [0 .. fromEnum u - 1])

-- | Specification for numbers with lower bound (inclusive) and upper bound (exclusive)
--
-- >>> runGenSymFresh (genSymFresh (EnumGenBound @Integer 0 4)) "c" :: UnionM Integer
-- UMrg (If c@0 (Single 0) (If c@1 (Single 1) (If c@2 (Single 2) (Single 3))))
data EnumGenBound a = EnumGenBound a a

instance (SymBoolOp bool, GenSymSimple () bool, Enum v, Mergeable bool v) => GenSym bool (EnumGenBound v) v where
  genSymFresh (EnumGenBound l u) = choose (toEnum <$> [fromEnum l .. fromEnum u - 1])

-- Either
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSymSimple a a,
    Mergeable bool a,
    GenSymSimple b b,
    Mergeable bool b
  ) =>
  GenSym bool (Either a b) (Either a b)

instance
  ( GenSymSimple a a,
    GenSymSimple b b
  ) =>
  GenSymSimple (Either a b) (Either a b)
  where
  genSymSimpleFresh = derivedSameShapeGenSymSimpleFresh

instance
  (SymBoolOp bool, GenSymSimple () bool, GenSym bool () a, Mergeable bool a, GenSym bool () b, Mergeable bool b) =>
  GenSym bool () (Either a b)
  where
  genSymFresh = derivedNoSpecGenSymFresh

-- Maybe
instance
  (SymBoolOp bool, GenSymSimple () bool, GenSymSimple a a, Mergeable bool a) =>
  GenSym bool (Maybe a) (Maybe a)

instance
  (GenSymSimple a a) =>
  GenSymSimple (Maybe a) (Maybe a)
  where
  genSymSimpleFresh = derivedSameShapeGenSymSimpleFresh

instance (SymBoolOp bool, GenSymSimple () bool, GenSym bool () a, Mergeable bool a) => GenSym bool () (Maybe a) where
  genSymFresh = derivedNoSpecGenSymFresh

-- List
instance
  (SymBoolOp bool, GenSymSimple () bool, GenSymSimple () a, Mergeable bool a) =>
  GenSym bool Integer [a]
  where
  genSymFresh v = do
    l <- gl v
    let xs = reverse $ scanr (:) [] l
    choose xs
    where
      gl :: (MonadGenSymFresh m) => Integer -> m [a]
      gl v1
        | v1 <= 0 = return []
        | otherwise = do
            l <- genSymSimpleFresh ()
            r <- gl (v1 - 1)
            return $ l : r

-- | Specification for list generation.
--
-- >>> runGenSymFresh (genSymFresh (ListSpec 0 2 ())) "c" :: UnionM [SymBool]
-- UMrg (If c@2 (Single []) (If c@3 (Single [c@1]) (Single [c@0,c@1])))
data ListSpec spec = ListSpec
  { -- | The minimum length of the generated lists
    genListMinLength :: Integer,
    -- | The maximum length of the generated lists
    genListMaxLength :: Integer,
    -- | Each element in the lists will be generated with the sub-specification
    genListSubSpec :: spec
  }
  deriving (Show)

instance
  (SymBoolOp bool, GenSymSimple () bool, GenSymSimple spec a, Mergeable bool a) =>
  GenSym bool (ListSpec spec) [a]
  where
  genSymFresh (ListSpec minLen maxLen subSpec) =
    if minLen < 0 || maxLen < 0 || minLen >= maxLen
      then error $ "Bad lengthes: " ++ show (minLen, maxLen)
      else do
        l <- gl maxLen
        let xs = drop (fromInteger minLen) $ reverse $ scanr (:) [] l
        choose xs
    where
      gl :: (MonadGenSymFresh m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
            l <- genSymSimpleFresh subSpec
            r <- gl (currLen - 1)
            return $ l : r

instance
  (SymBoolOp bool, GenSymSimple () bool, GenSymSimple a a, Mergeable bool a) =>
  GenSym bool [a] [a]

instance
  (GenSymSimple a a) =>
  GenSymSimple [a] [a]
  where
  genSymSimpleFresh = derivedSameShapeGenSymSimpleFresh

-- | Specification for list generation of a specific length.
--
-- >>> runGenSymFresh (genSymSimpleFresh (SimpleListSpec 2 ())) "c" :: [SymBool]
-- [c@0,c@1]
data SimpleListSpec spec = SimpleListSpec
  { -- | The length of the generated list
    genSimpleListLength :: Integer,
    -- | Each element in the list will be generated with the sub-specification
    genSimpleListSubSpec :: spec
  }
  deriving (Show)

instance
  (SymBoolOp bool, GenSymSimple () bool, GenSymSimple spec a, Mergeable bool a) =>
  GenSym bool (SimpleListSpec spec) [a]
  where
  genSymFresh = fmap mrgSingle . genSymSimpleFresh

instance
  (GenSymSimple spec a) =>
  GenSymSimple (SimpleListSpec spec) [a]
  where
  genSymSimpleFresh (SimpleListSpec len subSpec) =
    if len < 0
      then error $ "Bad lengthes: " ++ show len
      else do
        gl len
    where
      gl :: (MonadGenSymFresh m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
            l <- genSymSimpleFresh subSpec
            r <- gl (currLen - 1)
            return $ l : r

-- ()
instance (SymBoolOp bool, GenSymSimple () bool) => GenSym bool () ()

instance GenSymSimple () () where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b
  ) =>
  GenSym bool (aspec, bspec) (a, b)
  where
  genSymFresh (aspec, bspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    return $ do
      ax <- a1
      bx <- b1
      mrgSingle (ax, bx)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b
  ) =>
  GenSymSimple (aspec, bspec) (a, b)
  where
  genSymSimpleFresh (aspec, bspec) = do
    (,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec

instance
  (SymBoolOp bool, GenSymSimple () bool, GenSym bool () a, Mergeable bool a, GenSym bool () b, Mergeable bool b) =>
  GenSym bool () (a, b)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b
  ) =>
  GenSymSimple () (a, b)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c
  ) =>
  GenSym bool (aspec, bspec, cspec) (a, b, c)
  where
  genSymFresh (aspec, bspec, cspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      mrgSingle (ax, bx, cx)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b,
    GenSymSimple cspec c
  ) =>
  GenSymSimple (aspec, bspec, cspec) (a, b, c)
  where
  genSymSimpleFresh (aspec, bspec, cspec) = do
    (,,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec
      <*> genSymSimpleFresh cspec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c
  ) =>
  GenSym bool () (a, b, c)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b,
    GenSymSimple () c
  ) =>
  GenSymSimple () (a, b, c)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec) (a, b, c, d)
  where
  genSymFresh (aspec, bspec, cspec, dspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      mrgSingle (ax, bx, cx, dx)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b,
    GenSymSimple cspec c,
    GenSymSimple dspec d
  ) =>
  GenSymSimple (aspec, bspec, cspec, dspec) (a, b, c, d)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec) = do
    (,,,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec
      <*> genSymSimpleFresh cspec
      <*> genSymSimpleFresh dspec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d
  ) =>
  GenSym bool () (a, b, c, d)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b,
    GenSymSimple () c,
    GenSymSimple () d
  ) =>
  GenSymSimple () (a, b, c, d)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e)
  where
  genSymFresh (aspec, bspec, cspec, dspec, espec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      mrgSingle (ax, bx, cx, dx, ex)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b,
    GenSymSimple cspec c,
    GenSymSimple dspec d,
    GenSymSimple espec e
  ) =>
  GenSymSimple (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec) = do
    (,,,,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec
      <*> genSymSimpleFresh cspec
      <*> genSymSimpleFresh dspec
      <*> genSymSimpleFresh espec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e
  ) =>
  GenSym bool () (a, b, c, d, e)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b,
    GenSymSimple () c,
    GenSymSimple () d,
    GenSymSimple () e
  ) =>
  GenSymSimple () (a, b, c, d, e)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e,
    GenSym bool fspec f,
    Mergeable bool f
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f)
  where
  genSymFresh (aspec, bspec, cspec, dspec, espec, fspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    f1 <- genSymFresh fspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      fx <- f1
      mrgSingle (ax, bx, cx, dx, ex, fx)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b,
    GenSymSimple cspec c,
    GenSymSimple dspec d,
    GenSymSimple espec e,
    GenSymSimple fspec f
  ) =>
  GenSymSimple (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec) = do
    (,,,,,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec
      <*> genSymSimpleFresh cspec
      <*> genSymSimpleFresh dspec
      <*> genSymSimpleFresh espec
      <*> genSymSimpleFresh fspec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e,
    GenSym bool () f,
    Mergeable bool f
  ) =>
  GenSym bool () (a, b, c, d, e, f)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b,
    GenSymSimple () c,
    GenSymSimple () d,
    GenSymSimple () e,
    GenSymSimple () f
  ) =>
  GenSymSimple () (a, b, c, d, e, f)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e,
    GenSym bool fspec f,
    Mergeable bool f,
    GenSym bool gspec g,
    Mergeable bool g
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g)
  where
  genSymFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    f1 <- genSymFresh fspec
    g1 <- genSymFresh gspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      fx <- f1
      gx <- g1
      mrgSingle (ax, bx, cx, dx, ex, fx, gx)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b,
    GenSymSimple cspec c,
    GenSymSimple dspec d,
    GenSymSimple espec e,
    GenSymSimple fspec f,
    GenSymSimple gspec g
  ) =>
  GenSymSimple (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    (,,,,,,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec
      <*> genSymSimpleFresh cspec
      <*> genSymSimpleFresh dspec
      <*> genSymSimpleFresh espec
      <*> genSymSimpleFresh fspec
      <*> genSymSimpleFresh gspec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e,
    GenSym bool () f,
    Mergeable bool f,
    GenSym bool () g,
    Mergeable bool g
  ) =>
  GenSym bool () (a, b, c, d, e, f, g)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b,
    GenSymSimple () c,
    GenSymSimple () d,
    GenSymSimple () e,
    GenSymSimple () f,
    GenSymSimple () g
  ) =>
  GenSymSimple () (a, b, c, d, e, f, g)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- (,,,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool aspec a,
    Mergeable bool a,
    GenSym bool bspec b,
    Mergeable bool b,
    GenSym bool cspec c,
    Mergeable bool c,
    GenSym bool dspec d,
    Mergeable bool d,
    GenSym bool espec e,
    Mergeable bool e,
    GenSym bool fspec f,
    Mergeable bool f,
    GenSym bool gspec g,
    Mergeable bool g,
    GenSym bool hspec h,
    Mergeable bool h
  ) =>
  GenSym bool (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h)
  where
  genSymFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    a1 <- genSymFresh aspec
    b1 <- genSymFresh bspec
    c1 <- genSymFresh cspec
    d1 <- genSymFresh dspec
    e1 <- genSymFresh espec
    f1 <- genSymFresh fspec
    g1 <- genSymFresh gspec
    h1 <- genSymFresh hspec
    return $ do
      ax <- a1
      bx <- b1
      cx <- c1
      dx <- d1
      ex <- e1
      fx <- f1
      gx <- g1
      hx <- h1
      mrgSingle (ax, bx, cx, dx, ex, fx, gx, hx)

instance
  ( GenSymSimple aspec a,
    GenSymSimple bspec b,
    GenSymSimple cspec c,
    GenSymSimple dspec d,
    GenSymSimple espec e,
    GenSymSimple fspec f,
    GenSymSimple gspec g,
    GenSymSimple hspec h
  ) =>
  GenSymSimple (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    (,,,,,,,)
      <$> genSymSimpleFresh aspec
      <*> genSymSimpleFresh bspec
      <*> genSymSimpleFresh cspec
      <*> genSymSimpleFresh dspec
      <*> genSymSimpleFresh espec
      <*> genSymSimpleFresh fspec
      <*> genSymSimpleFresh gspec
      <*> genSymSimpleFresh hspec

instance
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c,
    GenSym bool () d,
    Mergeable bool d,
    GenSym bool () e,
    Mergeable bool e,
    GenSym bool () f,
    Mergeable bool f,
    GenSym bool () g,
    Mergeable bool g,
    GenSym bool () h,
    Mergeable bool h
  ) =>
  GenSym bool () (a, b, c, d, e, f, g, h)
  where
  genSymFresh = derivedNoSpecGenSymFresh

instance
  ( GenSymSimple () a,
    GenSymSimple () b,
    GenSymSimple () c,
    GenSymSimple () d,
    GenSymSimple () e,
    GenSymSimple () f,
    GenSymSimple () g,
    GenSymSimple () h
  ) =>
  GenSymSimple () (a, b, c, d, e, f, g, h)
  where
  genSymSimpleFresh = derivedNoSpecGenSymSimpleFresh

-- MaybeT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSym bool spec (MaybeT m a)
  where
  genSymFresh v = do
    x <- genSymFresh v
    return $ merge . fmap MaybeT $ x

instance
  {-# OVERLAPPABLE #-}
  ( GenSymSimple spec (m (Maybe a))
  ) =>
  GenSymSimple spec (MaybeT m a)
  where
  genSymSimpleFresh v = MaybeT <$> genSymSimpleFresh v

instance
  {-# OVERLAPPING #-}
  ( GenSymSimple (m (Maybe a)) (m (Maybe a))
  ) =>
  GenSymSimple (MaybeT m a) (MaybeT m a)
  where
  genSymSimpleFresh (MaybeT v) = MaybeT <$> genSymSimpleFresh v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSymSimple (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSym bool (MaybeT m a) (MaybeT m a)

-- ExceptT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSym bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  GenSym bool spec (ExceptT a m b)
  where
  genSymFresh v = do
    x <- genSymFresh v
    return $ merge . fmap ExceptT $ x

instance
  {-# OVERLAPPABLE #-}
  ( GenSymSimple spec (m (Either a b))
  ) =>
  GenSymSimple spec (ExceptT a m b)
  where
  genSymSimpleFresh v = ExceptT <$> genSymSimpleFresh v

instance
  {-# OVERLAPPING #-}
  ( GenSymSimple (m (Either e a)) (m (Either e a))
  ) =>
  GenSymSimple (ExceptT e m a) (ExceptT e m a)
  where
  genSymSimpleFresh (ExceptT v) = ExceptT <$> genSymSimpleFresh v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple () bool,
    GenSymSimple (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  GenSym bool (ExceptT e m a) (ExceptT e m a)
