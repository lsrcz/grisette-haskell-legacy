{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad.Except
import Control.Monad.Trans.Except
import Data.Functor.Classes
import GHC.Generics
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Functor
import Grisette.Data.SymPrim
import Unsafe.Coerce

newtype Either' a b = Either' {getEither' :: Either a b} deriving (Show, Generic)

instance (Show a) => Show1 (Either' a) where
  liftShowsPrec sp sl d (Either' e) = liftShowsPrec sp sl d e

instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b) => Mergeable bool (Either' a b) where
  mergeStrategy =
    OrderedStrategy
      ( \case
          (Either' (Left _)) -> 1 :: Int
          (Either' (Right _)) -> 0
      )
      ( \case
          0 -> wrapMergeStrategy mergeStrategy (Either' . Right) (\case Either' (Right x) -> x; _ -> error "Should not happen")
          1 -> wrapMergeStrategy mergeStrategy (Either' . Left) (\case Either' (Left x) -> x; _ -> error "Should not happen")
          _ -> error "Should not happen"
      )

newtype ExceptT' e m a = ExceptT' {runExceptT' :: m (Either' e a)} deriving (Generic, Generic1)

toExceptT :: ExceptT' e m a -> ExceptT e m a
toExceptT = unsafeCoerce

fromExceptT :: ExceptT e m a -> ExceptT' e m a
fromExceptT = unsafeCoerce

throwE' :: (Monad m) => e -> ExceptT' e m a
throwE' = fromExceptT . throwE

catchE' :: (Monad m) => ExceptT' e m a -> (e -> ExceptT' e' m a) -> ExceptT' e' m a
m `catchE'` h = fromExceptT $ toExceptT m `catchE` (toExceptT . h)

instance (Monad m) => MonadError e (ExceptT' e m) where
  throwError = throwE'
  catchError = catchE'

instance (Functor m) => Functor (ExceptT' e m) where
  fmap f = fromExceptT . fmap f . toExceptT

instance (Monad m) => Applicative (ExceptT' e m) where
  pure a = fromExceptT $ return a
  f <*> v = fromExceptT $ toExceptT f <*> toExceptT v

instance (Monad m) => Monad (ExceptT' e m) where
  return a = fromExceptT $ return a
  m >>= k = fromExceptT $ toExceptT m >>= (toExceptT . k)

instance (Show1 m, Show e) => Show1 (ExceptT' e m) where
  liftShowsPrec sp sl d (ExceptT' m) = showsUnaryWith (liftShowsPrec sp' sl') "ExceptT'" d m
    where
      sp' = liftShowsPrec sp sl
      sl' = liftShowList sp sl

instance (Show1 m, Show e, Show a) => Show (ExceptT' e m a) where
  showsPrec = showsPrec1

data Exceptions
  = AssertViolation
  | AssumeViolation
  deriving (Show, Generic)

instance (SymBoolOp bool) => Mergeable bool Exceptions

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e, Mergeable bool a) => Mergeable bool (ExceptT' e m a) where
  mergeStrategy = withMergeable @bool @m @(Either' e a) $ derivedMergeStrategy

instance (SymBoolOp bool, Mergeable1 bool m, Mergeable bool e) => Mergeable1 bool (ExceptT' e m)

instance (SymBoolOp bool, UnionMOp bool m, Mergeable bool e, Mergeable bool a) => SimpleMergeable bool (ExceptT' e m a) where
  mrgIf c t f = withUnionMSimpleMergeable @bool @m @(Either' e a) $ ExceptT' $ mrgIf c (runExceptT' t) (runExceptT' f)

instance (SymBoolOp bool, UnionMOp bool m, Mergeable bool e) => SimpleMergeable1 bool (ExceptT' e m)

instance (SymBoolOp bool, UnionMOp bool m, Mergeable bool e) => UnionMOp bool (ExceptT' e m) where
  merge = ExceptT' . merge . runExceptT'
  mrgSingle = ExceptT' . mrgSingle . Either' . Right
  mrgGuard = mrgIf

assertWithError :: forall m b ex. (MonadError ex m, SymBoolOp b, UnionMOp b m) => ex -> b -> m ()
assertWithError ex x = mrgGuard x (return ()) (throwError ex)

assert :: forall m b. (MonadError Exceptions m, SymBoolOp b, UnionMOp b m) => b -> m ()
assert = assertWithError AssertViolation

assume :: forall m b. (MonadError Exceptions m, SymBoolOp b, UnionMOp b m) => b -> m ()
assume = assertWithError AssumeViolation

test :: forall exceptT. (MonadError Exceptions (exceptT Exceptions UnionM), UnionMOp SymBool (exceptT Exceptions UnionM)) => exceptT Exceptions UnionM SymBool
test =
  mrgGuard
    (ssymb "a")
    ( do
        assert $ ssymb "assert"
        return $ ssymb "x"
    )
    ( do
        assume $ ssymb "assume"
        return $ ssymb "y"
    )

test2 :: forall exceptT. (MonadError Exceptions (exceptT Exceptions UnionM), UnionMOp SymBool (exceptT Exceptions UnionM)) => exceptT Exceptions UnionM SymBool
test2 = do
  assert $ ssymb "x"
  r <-
    mrgGuard
      (ssymb "c")
      ( do
          assert $ ssymb "a1"
          return $ ssymb "r1"
      )
      ( do
          assert $ ssymb "a2"
          -- assume (ssymb "assume")
          return $ ssymb "r2"
      )
  assert $ ssymb "y"
  mrgReturn r

test3 :: forall exceptT. (MonadError Exceptions (exceptT Exceptions UnionM), UnionMOp SymBool (exceptT Exceptions UnionM)) => exceptT Exceptions UnionM ()
test3 = do
  assert $ ssymb "x"
  assume $ ssymb "y"
  assert $ ssymb "z"
  assume $ ssymb "k"

main :: IO ()
main = do
  -- ExceptT (UMrg (Guard (ite a (! assert) (! assume)) (Guard a (Single (Left AssertViolation)) (Single (Left AssumeViolation))) (Single (Right (ite a x y)))))
  print $ test @ExceptT
  -- UMrg (Single (&& (! (ite a (! assert) (! assume))) (ite a x y)))
  print $ mrgFmap (\case Left _ -> conc False; Right x -> x) $ runExceptT test
  -- ExceptT' (UMrg (Guard (ite a assert assume) (Single (Right (ite a x y))) (Guard a (Single (Left AssertViolation)) (Single (Left AssumeViolation)))))
  print $ test @ExceptT'
  -- UMrg (Single (&& (ite a assert assume) (ite a x y)))
  print $ mrgFmap (\case (Either' (Left _)) -> conc False; (Either' (Right x)) -> x) $ runExceptT' test
  putStrLn "2222"
  print $ test2 @ExceptT
  print $ test2 @ExceptT'
  print $ test3 @ExceptT
  print $ test3 @ExceptT'
  print $ mrgFmap (\case (Left AssertViolation) -> conc @SymBool True; _ -> conc False) $ runExceptT test3
  print $ mrgFmap (\case (Either' (Left AssertViolation)) -> conc @SymBool True; _ -> conc False) $ runExceptT' test3
