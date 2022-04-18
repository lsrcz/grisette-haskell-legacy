{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveAnyClass #-}

module Grisette.Data.Class.GenSym
  ( GenSymIndex (..),
    GenSymIdent,
    pattern GenSymIdent,
    pattern GenSymIdentWithInfo,
    name,
    nameWithInfo,
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
    NumGenBound (..),
    NumGenUpperBound (..),
  )
where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import Data.Bifunctor
import Data.String
import Data.Typeable
import Generics.Deriving hiding (index)
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Control.Monad.Signatures
import Language.Haskell.TH.Syntax hiding (lift)
import Control.DeepSeq
import Data.Hashable

-- | Index type used for 'GenSym'.
--
-- To generate fresh variables, a monadic stateful context will be maintained.
-- Every time a new variable is generated, the index will be increased.
newtype GenSymIndex = GenSymIndex Int
  deriving (Show)
  deriving (Eq, Ord, Num) via Int

instance (SymBoolOp bool) => Mergeable bool GenSymIndex where
  mergeStrategy = SimpleStrategy $ \_ t f -> max t f

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
--     s_a
--
--   * bundle the calling file location with the name to ensure global uniqueness
--
-- >>> $$(nameWithLoc "a")
-- a:<interactive>:4:4-18
--
--   * bundle the calling file location with some user provided information
--
-- >>> nameWithInfo "a" (1 :: Int)
-- a:1
--
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

-- | A symbolic generation monad transformer.
-- It is a reader monad transformer for identifiers and
-- a state monad transformer for indices.
--
-- Each time a fresh symbolic variable is generated, the index should be increased.
newtype GenSymFreshT m a = GenSymFreshT {runGenSymFreshT' :: GenSymIdent -> GenSymIndex -> m (a, GenSymIndex)}

instance (SymBoolOp bool, Mergeable bool a, Mergeable1 bool m) =>
  Mergeable bool (GenSymFreshT m a) where
  mergeStrategy =
    withMergeable @bool @m @(a, GenSymIndex) $
      withMergeable @bool @((->) GenSymIndex) @(m (a, GenSymIndex)) $
        withMergeable @bool @((->) GenSymIdent) @(GenSymIndex -> m (a, GenSymIndex)) $
          wrapMergeStrategy mergeStrategy GenSymFreshT runGenSymFreshT'

instance (SymBoolOp bool, Mergeable1 bool m) => Mergeable1 bool (GenSymFreshT m)

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m, Mergeable bool a) =>
  SimpleMergeable bool (GenSymFreshT m a) where
    mrgIte cond (GenSymFreshT t) (GenSymFreshT f) =
      withUnionSimpleMergeable @bool @m @(a, GenSymIndex) $ GenSymFreshT $ mrgIte cond t f

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m) =>
  SimpleMergeable1 bool (GenSymFreshT m) 

instance (SymBoolOp bool, UnionSimpleMergeable1 bool m) =>
  UnionSimpleMergeable1 bool (GenSymFreshT m)

instance (SymBoolOp bool, MonadUnion bool m) => 
  MonadUnion bool (GenSymFreshT m) where
  merge (GenSymFreshT f) = GenSymFreshT $ \ident index -> merge $ f ident index
  mrgReturn v = GenSymFreshT $ \_ index -> mrgReturn (v, index)
  mrgIf cond (GenSymFreshT t) (GenSymFreshT f) =
    GenSymFreshT $ \ident index -> mrgIf cond (t ident index) (f ident index)

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
  return a = GenSymFreshT $ \_ idx -> return (a, idx)
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

instance (Monad m) => MonadState GenSymIndex (GenSymFreshT m) where
  state f = GenSymFreshT $ \_ idx -> return $ f idx
  put newidx = GenSymFreshT $ \_ _ -> return ((), newidx)
  get = GenSymFreshT $ \_ idx -> return (idx, idx)

instance (Monad m) => MonadReader GenSymIdent (GenSymFreshT m) where
  ask = GenSymFreshT $ curry return
  local f (GenSymFreshT s) = GenSymFreshT $ \ident idx -> s (f ident) idx
  reader f = GenSymFreshT $ \r s -> return (f r, s)

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
  -- UMrg (Single s_a@0)
  --
  -- The following example generates booleans, which cannot be merged into a single value with type 'Bool'.
  -- No specification is needed.
  --
  -- >>> runGenSymFresh (genSymFresh ()) "a" :: UnionM Bool
  -- UMrg (Guard s_a@0 (Single False) (Single True))
  --
  -- The following example generates @Maybe Bool@s.
  -- There are more than one symbolic primitives introduced, and their uniqueness is ensured.
  -- No specification is needed.
  --
  -- >>> runGenSymFresh (genSymFresh ()) "a" :: UnionM (Maybe Bool)
  -- UMrg (Guard s_a@0 (Single Nothing) (Guard s_a@1 (Single (Just False)) (Single (Just True))))
  --
  -- The following example generates lists of symbolic booleans with length 1 to 2.
  --
  -- >>> runGenSymFresh (genSymFresh (ListSpec 1 2 ())) "a" :: UnionM [SymBool]
  -- UMrg (Guard s_a@2 (Single [s_a@1]) (Single [s_a@0,s_a@1]))
  --
  -- When multiple symbolic variables are generated, the uniqueness can be ensured.
  --
  -- >>> runGenSymFresh (do; a <- genSymFresh (); b <- genSymFresh (); return (a, b)) "a" :: (UnionM SymBool, UnionM SymBool)
  -- (UMrg (Single s_a@0),UMrg (Single s_a@1))
  --
  -- N.B.: the examples are not executable solely with @grisette-core@ package, and need support from @grisette-symprim@ package.
  genSymFresh ::
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m,
      MonadUnion bool u
    ) =>
    spec ->
    m (u a)
  default genSymFresh ::
    (GenSymSimple bool spec a) =>
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m,
      MonadUnion bool u
    ) =>
    spec ->
    m (u a)
  genSymFresh spec = mrgReturn @bool <$> genSymSimpleFresh @bool spec

-- | Generate a symbolic variable wrapped in a Union without the monadic context.
-- The uniqueness need to be ensured by the uniqueness of the provided identifier.
genSym :: (GenSym bool spec a, MonadUnion bool u) => spec -> GenSymIdent -> u a
genSym = runGenSymFresh . genSymFresh

-- | Class of types in which symbolic values can be generated with respect to some specification.
--
-- The result will __/not/__ be wrapped in a union-like monad.
--
-- The uniqueness with be managed with the a monadic context. 'GenSymFresh' and 'GenSymFreshT' can be useful.
class GenSym bool spec a => GenSymSimple bool spec a where
  -- | Generate a symbolic value given some specification. The uniqueness is ensured.
  --
  -- The following example generates a symbolic boolean. No specification is needed.
  -- As the symbolic primitive implementations are decoupled from the core Grisette constructs in the system,
  -- The user need to tell the system which set of symbolic primitives to use (by telling the system the symbolic boolean types).
  -- Thus the type application to 'SymBool' is necessary here.
  --
  -- >>> :set -XTypeApplications
  -- >>> runGenSymFresh (genSymSimpleFresh @SymBool ()) "a" :: SymBool
  -- s_a@0
  --
  -- The example shows that why the system cannot infer the symbolic boolean type.
  --
  -- >>> runGenSymFresh (genSymSimpleFresh @SymBool ()) "a" :: ()
  -- ()
  --
  -- The following code generates list of symbolic boolean with length 2.
  -- As the length is fixed, we don't have to wrap the result in unions.
  --
  -- >>> runGenSymFresh (genSymSimpleFresh @SymBool (SimpleListSpec 2 ())) "a" :: [SymBool]
  --
  -- N.B.: the examples are not executable solely with @grisette-core@ package, and need support from @grisette-symprim@ package.
  genSymSimpleFresh ::
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m
    ) =>
    spec ->
    m a

-- | Generate a simple symbolic variable wrapped in a Union without the monadic context.
-- The uniqueness need to be ensured by the uniqueness of the provided identifier.
genSymSimple :: forall bool spec a. (GenSymSimple bool spec a) => spec -> GenSymIdent -> a
genSymSimple = runGenSymFresh . (genSymSimpleFresh @bool)

class GenSymNoSpec bool a where
  genSymFreshNoSpec ::
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m,
      MonadUnion bool u
    ) =>
    m (u (a c))

instance (SymBoolOp bool) => GenSymNoSpec bool U1 where
  genSymFreshNoSpec = return $ mrgReturn U1

instance (SymBoolOp bool, GenSym bool () c) => GenSymNoSpec bool (K1 i c) where
  genSymFreshNoSpec = fmap K1 <$> genSymFresh ()

instance (SymBoolOp bool, GenSymNoSpec bool a) => GenSymNoSpec bool (M1 i c a) where
  genSymFreshNoSpec = fmap M1 <$> genSymFreshNoSpec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymNoSpec bool a,
    GenSymNoSpec bool b,
    forall x. Mergeable bool (a x),
    forall x. Mergeable bool (b x)
  ) =>
  GenSymNoSpec bool (a :+: b)
  where
  genSymFreshNoSpec ::
    forall m u c.
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m,
      MonadUnion bool u
    ) =>
    m (u ((a :+: b) c))
  genSymFreshNoSpec = do
    cond :: bool <- genSymSimpleFresh @bool ()
    l :: u (a c) <- genSymFreshNoSpec
    r :: u (b c) <- genSymFreshNoSpec
    return $ mrgIf cond (fmap L1 l) (fmap R1 r)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymNoSpec bool a, GenSymNoSpec bool b) =>
  GenSymNoSpec bool (a :*: b)
  where
  genSymFreshNoSpec ::
    forall m u c.
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m,
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
    MonadState GenSymIndex m,
    MonadReader GenSymIdent m,
    MonadUnion bool u
  ) =>
  m (u a)
derivedNoSpecGenSymFresh = mrgFmap to <$> genSymFreshNoSpec @bool @(Rep a)

class GenSymSimpleNoSpec bool a where
  genSymSimpleFreshNoSpec :: (MonadState GenSymIndex m, MonadReader GenSymIdent m) => m (a c)

instance (SymBoolOp bool) => GenSymSimpleNoSpec bool U1 where
  genSymSimpleFreshNoSpec = return U1

instance (SymBoolOp bool, GenSymSimple bool () c) => GenSymSimpleNoSpec bool (K1 i c) where
  genSymSimpleFreshNoSpec = K1 <$> genSymSimpleFresh @bool ()

instance (SymBoolOp bool, GenSymSimpleNoSpec bool a) => GenSymSimpleNoSpec bool (M1 i c a) where
  genSymSimpleFreshNoSpec = M1 <$> genSymSimpleFreshNoSpec @bool

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimpleNoSpec bool a, GenSymSimpleNoSpec bool b) =>
  GenSymSimpleNoSpec bool (a :*: b)
  where
  genSymSimpleFreshNoSpec = do
    l :: a c <- genSymSimpleFreshNoSpec @bool
    r :: b c <- genSymSimpleFreshNoSpec @bool
    return $ l :*: r

-- | We cannot provide DerivingVia style derivation for 'GenSymSimple'.
--
-- This 'genSymSimpleFresh' implementation is for the types that does not need any specification.
-- It will generate product types by generating each fields with '()' as specification.
-- It will not work on sum types.
-- 
-- N.B. Never use on recursive types
derivedNoSpecGenSymSimpleFresh ::
  forall bool a m.
  ( Generic a,
    SymBoolOp bool,
    GenSymSimpleNoSpec bool (Rep a),
    MonadState GenSymIndex m,
    MonadReader GenSymIdent m
  ) =>
  m a
derivedNoSpecGenSymSimpleFresh = to <$> genSymSimpleFreshNoSpec @bool @(Rep a)

class GenSymSameShape bool a where
  genSymSameShapeFresh ::
    ( MonadState GenSymIndex m,
      MonadReader GenSymIdent m
    ) =>
    a c ->
    m (a c)

instance (SymBoolOp bool) => GenSymSameShape bool U1 where
  genSymSameShapeFresh _ = return U1

instance (SymBoolOp bool, GenSymSimple bool c c) => GenSymSameShape bool (K1 i c) where
  genSymSameShapeFresh (K1 c) = K1 <$> genSymSimpleFresh @bool c

instance (SymBoolOp bool, GenSymSameShape bool a) => GenSymSameShape bool (M1 i c a) where
  genSymSameShapeFresh (M1 a) = M1 <$> genSymSameShapeFresh @bool a

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSameShape bool a, GenSymSameShape bool b) =>
  GenSymSameShape bool (a :+: b)
  where
  genSymSameShapeFresh (L1 a) = L1 <$> genSymSameShapeFresh @bool a
  genSymSameShapeFresh (R1 a) = R1 <$> genSymSameShapeFresh @bool a

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSameShape bool a, GenSymSameShape bool b) =>
  GenSymSameShape bool (a :*: b)
  where
  genSymSameShapeFresh (a :*: b) = do
    l :: a c <- genSymSameShapeFresh @bool a
    r :: b c <- genSymSameShapeFresh @bool b
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
  forall bool a m.
  ( Generic a,
    GenSymSameShape bool (Rep a),
    MonadState GenSymIndex m,
    MonadReader GenSymIdent m
  ) =>
  a ->
  m a
derivedSameShapeGenSymSimpleFresh a = to <$> genSymSameShapeFresh @bool @(Rep a) (from a)

-- | Symbolically chooses one of the provided values.
-- The procedure creates @n - 1@ fresh symbolic boolean variables every time it is evaluated, and use
-- these variables to conditionally select one of the @n@ provided expressions.
--
-- The result will be wrapped in a union-like monad, and also a monad maintaining the 'GenSym' context.
--
-- >>> runGenSymFresh (choose [1,2,3]) "a" :: UnionM Integer
-- UMrg (Guard s_a@0 (Single 1) (Guard s_a@1 (Single 2) (Single 3)))
choose ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    GenSymSimple bool () bool,
    MonadState GenSymIndex m,
    MonadReader GenSymIdent m,
    MonadUnion bool u
  ) =>
  [a] ->
  m (u a)
choose [x] = return $ mrgReturn x
choose (r : rs) = do
  b <- genSymSimpleFresh @bool ()
  res <- choose rs
  return $ mrgIf b (mrgReturn r) res
choose [] = error "choose expects at least one value"

-- | Symbolically chooses one of the provided values.
-- The procedure creates @n - 1@ fresh symbolic boolean variables every time it is evaluated, and use
-- these variables to conditionally select one of the @n@ provided expressions.
--
-- The result will __/not/__ be wrapped in a union-like monad, but will be wrapped in a monad maintaining the 'GenSym' context.
-- Similar to 'genSymSimpleFresh', you need to tell the system what symbolic boolean type to use.
--
-- >>> runGenSymFresh (simpleChoose @SymBool [ssymb "b", ssymb "c", ssymb "d"]) "a" :: SymInteger
-- (ite s_a@0 b (ite s_a@1 c d))
simpleChoose ::
  forall bool a m.
  ( SymBoolOp bool,
    SimpleMergeable bool a,
    GenSymSimple bool () bool,
    MonadState GenSymIndex m,
    MonadReader GenSymIdent m
  ) =>
  [a] ->
  m a
simpleChoose [x] = return x
simpleChoose (r : rs) = do
  b <- genSymSimpleFresh @bool ()
  res <- simpleChoose @bool rs
  return $ mrgIte @bool b r res
simpleChoose [] = error "simpleChoose expects at least one value"

-- | Symbolically chooses one of the provided values wrapped in union-like monads.
-- The procedure creates @n - 1@ fresh symbolic boolean variables every time it is evaluated, and use
-- these variables to conditionally select one of the @n@ provided expressions.
--
-- The result will be wrapped in a union-like monad, and also a monad maintaining the 'GenSym' context.
--
-- >>> let a = runGenSymFresh (choose [1, 2]) "a" :: UnionM Integer
-- >>> let b = runGenSymFresh (choose [2, 3]) "b" :: UnionM Integer
-- >>> runGenSymFresh (chooseU [a, b]) "c" :: UnionM Integer
-- UMrg (Guard (&& s_c@0 s_a@0) (Single 1) (Guard (|| s_c@0 s_b@0) (Single 2) (Single 3)))
chooseU ::
  forall bool a m u.
  ( SymBoolOp bool,
    Mergeable bool a,
    GenSymSimple bool () bool,
    MonadState GenSymIndex m,
    MonadReader GenSymIdent m,
    MonadUnion bool u
  ) =>
  [u a] ->
  m (u a)
chooseU [x] = return x
chooseU (r : rs) = do
  b <- genSymSimpleFresh @bool ()
  res <- chooseU rs
  return $ mrgIf b r res
chooseU [] = error "chooseU expects at least one value"

-- Bool
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool Bool Bool where
  genSymFresh v = return $ mrgReturn v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool Bool Bool where
  genSymSimpleFresh v = return v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool () Bool where
  genSymFresh _ = derivedNoSpecGenSymFresh

-- Integer
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool Integer Integer where
  genSymFresh v = return $ mrgReturn v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool Integer Integer where
  genSymSimpleFresh v = return v

-- | Specification for numbers with upper bound (inclusive). The result would chosen from [0 .. upperbound].
--
-- >>> runGenSymFresh (genSymFresh (NumGenUpperBound @Integer 3)) "c" :: UnionM Integer
-- UMrg (Guard s_c@0 (Single 0) (Guard s_c@1 (Single 1) (Guard s_c@2 (Single 2) (Single 3))))
newtype NumGenUpperBound a = NumGenUpperBound a

-- | Specification for numbers with lower bound and upper bound (inclusive)
--
-- >>> runGenSymFresh (genSymFresh (NumGenBound @Integer 0 3)) "c" :: UnionM Integer
-- UMrg (Guard s_c@0 (Single 0) (Guard s_c@1 (Single 1) (Guard s_c@2 (Single 2) (Single 3))))
data NumGenBound a = NumGenBound a a

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenUpperBound Integer) Integer where
  genSymFresh (NumGenUpperBound upperBound) =
    if upperBound < 0
      then error $ "Bad upper bound (should be >= 0): " ++ show upperBound
      else choose [0, 1 .. upperBound]

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenBound Integer) Integer where
  genSymFresh (NumGenBound l u) =
    if u < l
      then error $ "Bad bounds (upper bound should >= lower bound): " ++ show (l, u)
      else choose [l, l + 1 .. u]

-- Char
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool Char Char where
  genSymFresh v = return $ mrgReturn v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool Char Char where
  genSymSimpleFresh v = return v

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenUpperBound Char) Char where
  genSymFresh (NumGenUpperBound upperBound) = choose (toEnum <$> [0 .. fromEnum upperBound - 1])

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool (NumGenBound Char) Char where
  genSymFresh (NumGenBound l u) = choose (toEnum <$> [fromEnum l .. fromEnum u - 1])

-- Either
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool a a,
    Mergeable bool a,
    GenSymSimple bool b b,
    Mergeable bool b
  ) =>
  GenSym bool (Either a b) (Either a b)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool a a,
    Mergeable bool a,
    GenSymSimple bool b b,
    Mergeable bool b
  ) =>
  GenSymSimple bool (Either a b) (Either a b)
  where
  genSymSimpleFresh v = derivedSameShapeGenSymSimpleFresh @bool v

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSym bool () a, Mergeable bool a, GenSym bool () b, Mergeable bool b) =>
  GenSym bool () (Either a b)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

-- Maybe
instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSym bool (Maybe a) (Maybe a)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSymSimple bool (Maybe a) (Maybe a)
  where
  genSymSimpleFresh v = derivedSameShapeGenSymSimpleFresh @bool v

instance (SymBoolOp bool, GenSymSimple bool () bool, GenSym bool () a, Mergeable bool a) => GenSym bool () (Maybe a) where
  genSymFresh _ = derivedNoSpecGenSymFresh

-- List
instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool () a, Mergeable bool a) =>
  GenSym bool Integer [a]
  where
  genSymFresh v = do
    l <- gl v
    let xs = reverse $ scanr (:) [] l
    choose xs
    where
      gl :: (MonadState GenSymIndex m, MonadReader GenSymIdent m) => Integer -> m [a]
      gl v1
        | v1 <= 0 = return []
        | otherwise = do
          l <- genSymSimpleFresh @bool ()
          r <- gl (v1 - 1)
          return $ l : r

-- | Specification for list generation.
--
-- >>> runGenSymFresh (genSymFresh (ListSpec 0 2 ())) "c" :: UnionM [SymBool]
-- UMrg (Guard s_c@2 (Single []) (Guard s_c@3 (Single [s_c@1]) (Single [s_c@0,s_c@1])))
data ListSpec spec = ListSpec
  { genListMinLength :: Integer, -- ^ The minimum length of the generated lists
    genListMaxLength :: Integer, -- ^ The maximum length of the generated lists
    genListSubSpec :: spec       -- ^ Each element in the lists will be generated with the sub-specification
  }
  deriving (Show)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec a, Mergeable bool a) =>
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
      gl :: (MonadState GenSymIndex m, MonadReader GenSymIdent m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
          l <- genSymSimpleFresh @bool subSpec
          r <- gl (currLen - 1)
          return $ l : r

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSym bool [a] [a]

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool a a, Mergeable bool a) =>
  GenSymSimple bool [a] [a]
  where
  genSymSimpleFresh v = derivedSameShapeGenSymSimpleFresh @bool v

-- | Specification for list generation of a specific length.
--
-- >>> runGenSymFresh (genSymSimpleFresh @SymBool (SimpleListSpec 2 ())) "c" :: [SymBool]
-- [s_c@0,s_c@1]
data SimpleListSpec spec = SimpleListSpec
  { genSimpleListLength :: Integer, -- ^ The length of the generated list
    genSimpleListSubSpec :: spec    -- ^ Each element in the list will be generated with the sub-specification
  }
  deriving (Show)

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec a, Mergeable bool a) =>
  GenSym bool (SimpleListSpec spec) [a]
  where
  genSymFresh = fmap mrgReturn . genSymSimpleFresh @bool

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSymSimple bool spec a, Mergeable bool a) =>
  GenSymSimple bool (SimpleListSpec spec) [a]
  where
  genSymSimpleFresh (SimpleListSpec len subSpec) =
    if len < 0
      then error $ "Bad lengthes: " ++ show len
      else do
        gl len
    where
      gl :: (MonadState GenSymIndex m, MonadReader GenSymIdent m) => Integer -> m [a]
      gl currLen
        | currLen <= 0 = return []
        | otherwise = do
          l <- genSymSimpleFresh @bool subSpec
          r <- gl (currLen - 1)
          return $ l : r

-- ()
instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSym bool () ()

instance (SymBoolOp bool, GenSymSimple bool () bool) => GenSymSimple bool () () where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b
  ) =>
  GenSymSimple bool (aspec, bspec) (a, b)
  where
  genSymSimpleFresh (aspec, bspec) = do
    (,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec

instance
  (SymBoolOp bool, GenSymSimple bool () bool, GenSym bool () a, Mergeable bool a, GenSym bool () b, Mergeable bool b) =>
  GenSym bool () (a, b)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b
  ) =>
  GenSymSimple bool () (a, b)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx, cx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c
  ) =>
  GenSymSimple bool (aspec, bspec, cspec) (a, b, c)
  where
  genSymSimpleFresh (aspec, bspec, cspec) = do
    (,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool () a,
    Mergeable bool a,
    GenSym bool () b,
    Mergeable bool b,
    GenSym bool () c,
    Mergeable bool c
  ) =>
  GenSym bool () (a, b, c)
  where
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c
  ) =>
  GenSymSimple bool () (a, b, c)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx, cx, dx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec) (a, b, c, d)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec) = do
    (,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d
  ) =>
  GenSymSimple bool () (a, b, c, d)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx, cx, dx, ex)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec) (a, b, c, d, e)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec) = do
    (,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e
  ) =>
  GenSymSimple bool () (a, b, c, d, e)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx, cx, dx, ex, fx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e,
    GenSymSimple bool fspec f,
    Mergeable bool f
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec, fspec) (a, b, c, d, e, f)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec) = do
    (,,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec
      <*> genSymSimpleFresh @bool fspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e,
    GenSymSimple bool () f,
    Mergeable bool f
  ) =>
  GenSymSimple bool () (a, b, c, d, e, f)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx, cx, dx, ex, fx, gx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e,
    GenSymSimple bool fspec f,
    Mergeable bool f,
    GenSymSimple bool gspec g,
    Mergeable bool g
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec, fspec, gspec) (a, b, c, d, e, f, g)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec) = do
    (,,,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec
      <*> genSymSimpleFresh @bool fspec
      <*> genSymSimpleFresh @bool gspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e,
    GenSymSimple bool () f,
    Mergeable bool f,
    GenSymSimple bool () g,
    Mergeable bool g
  ) =>
  GenSymSimple bool () (a, b, c, d, e, f, g)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- (,,,,,,,)
instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
      mrgReturn (ax, bx, cx, dx, ex, fx, gx, hx)

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool aspec a,
    Mergeable bool a,
    GenSymSimple bool bspec b,
    Mergeable bool b,
    GenSymSimple bool cspec c,
    Mergeable bool c,
    GenSymSimple bool dspec d,
    Mergeable bool d,
    GenSymSimple bool espec e,
    Mergeable bool e,
    GenSymSimple bool fspec f,
    Mergeable bool f,
    GenSymSimple bool gspec g,
    Mergeable bool g,
    GenSymSimple bool hspec h,
    Mergeable bool h
  ) =>
  GenSymSimple bool (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) (a, b, c, d, e, f, g, h)
  where
  genSymSimpleFresh (aspec, bspec, cspec, dspec, espec, fspec, gspec, hspec) = do
    (,,,,,,,)
      <$> genSymSimpleFresh @bool aspec
      <*> genSymSimpleFresh @bool bspec
      <*> genSymSimpleFresh @bool cspec
      <*> genSymSimpleFresh @bool dspec
      <*> genSymSimpleFresh @bool espec
      <*> genSymSimpleFresh @bool fspec
      <*> genSymSimpleFresh @bool gspec
      <*> genSymSimpleFresh @bool hspec

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
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
  genSymFresh _ = derivedNoSpecGenSymFresh

instance
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool () a,
    Mergeable bool a,
    GenSymSimple bool () b,
    Mergeable bool b,
    GenSymSimple bool () c,
    Mergeable bool c,
    GenSymSimple bool () d,
    Mergeable bool d,
    GenSymSimple bool () e,
    Mergeable bool e,
    GenSymSimple bool () f,
    Mergeable bool f,
    GenSymSimple bool () g,
    Mergeable bool g,
    GenSymSimple bool () h,
    Mergeable bool h
  ) =>
  GenSymSimple bool () (a, b, c, d, e, f, g, h)
  where
  genSymSimpleFresh _ = derivedNoSpecGenSymSimpleFresh @bool

-- MaybeT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSym bool spec (MaybeT m a)
  where
  genSymFresh v = do
    x <- genSymFresh @bool v
    return $ mrgFmap MaybeT x

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool spec (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSymSimple bool spec (MaybeT m a)
  where
  genSymSimpleFresh v = MaybeT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSymSimple bool (MaybeT m a) (MaybeT m a)
  where
  genSymSimpleFresh (MaybeT v) = MaybeT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Maybe a)) (m (Maybe a)),
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  GenSym bool (MaybeT m a) (MaybeT m a)

-- ExceptT
instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSym bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  GenSym bool spec (ExceptT a m b)
  where
  genSymFresh v = do
    x <- genSymFresh @bool v
    return $ mrgFmap ExceptT x

instance
  {-# OVERLAPPABLE #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool spec (m (Either a b)),
    Mergeable1 bool m,
    Mergeable bool a,
    Mergeable bool b
  ) =>
  GenSymSimple bool spec (ExceptT a m b)
  where
  genSymSimpleFresh v = ExceptT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  GenSymSimple bool (ExceptT e m a) (ExceptT e m a)
  where
  genSymSimpleFresh (ExceptT v) = ExceptT <$> genSymSimpleFresh @bool v

instance
  {-# OVERLAPPING #-}
  ( SymBoolOp bool,
    GenSymSimple bool () bool,
    GenSymSimple bool (m (Either e a)) (m (Either e a)),
    Mergeable1 bool m,
    Mergeable bool e,
    Mergeable bool a
  ) =>
  GenSym bool (ExceptT e m a) (ExceptT e m a)
