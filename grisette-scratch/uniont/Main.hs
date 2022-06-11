{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
module Main where
import Grisette
import Grisette.Internal.Core

import Control.Monad
import Data.Functor.Classes
import Control.Monad.IO.Class
import Control.Monad.Trans
-- import Data.IORef
import Data.Functor

data UnionBaseM bool m a
  = UTSingle a
  | UTIf bool (m (UnionBaseM bool m a, UnionBaseM bool m a))

newtype UnionBaseMT bool m a = UnionBaseMT { runUnionBaseMT :: m (UnionBaseM bool m a)}

runUnionBaseMTAll :: (SymBoolOp bool, Monad m) => UnionBaseMT bool m a -> m (UnionBase bool a)
runUnionBaseMTAll (UnionBaseMT v) = do
  v1 <- v
  go v1
  where
    go (UTSingle a) = return $ Single a
    go (UTIf cond mlr) = do
      (l, r) <- mlr
      l1 <- go l
      r1 <- go r
      return $ ifWithLeftMost False cond l1 r1


ifMT :: (SymBoolOp bool, Monad m) => bool -> UnionBaseMT bool m a -> UnionBaseMT bool m a -> UnionBaseMT bool m a
ifMT cond (UnionBaseMT l) (UnionBaseMT r) = UnionBaseMT $ do
  l1 <- l
  r1 <- r
  return $ UTIf cond (return (l1, r1))

bind :: (Monad m, SymBoolOp bool) => UnionBaseMT bool m a -> (a -> UnionBaseMT bool m b) -> UnionBaseMT bool m b
bind x f = UnionBaseMT $ do
  x' <- runUnionBaseMT x
  case x' of
    UTSingle a -> runUnionBaseMT $ f a
    UTIf bool mas -> do
      (asl, asr) <- mas
      return $ UTIf bool (do
        l1 <- runUnionBaseMT $ bind (UnionBaseMT $ return asl) f
        r1 <- runUnionBaseMT $ bind (UnionBaseMT $ return asr) f
        return (l1, r1))

instance (Functor m) => Functor (UnionBaseM bool m) where
  fmap f (UTSingle x) = UTSingle $ f x
  fmap f (UTIf cond mlr) = UTIf cond $ (\(a, b) -> (f <$> a, f <$> b)) <$> mlr

instance (Functor m) => Functor (UnionBaseMT bool m) where
  fmap f x = UnionBaseMT $ runUnionBaseMT x <&> (\case
    UTSingle a -> UTSingle $ f a
    UTIf cond mlr -> UTIf cond $ (\(a, b) -> (f <$> a, f <$> b)) <$> mlr
    )

instance (SymBoolOp bool, Monad m) => Applicative (UnionBaseMT bool m) where
  pure x = UnionBaseMT $ pure $ UTSingle x
  fs <*> xs = do
    f <- fs
    x <- xs
    pure (f x)

instance (SymBoolOp bool, Monad m) => Monad (UnionBaseMT bool m) where
  (>>=) = bind

instance (SymBoolOp bool) => MonadTrans (UnionBaseMT bool) where
  lift x = UnionBaseMT $ UTSingle <$> x

instance (SymBoolOp bool, MonadIO m) => MonadIO (UnionBaseMT bool m) where
  liftIO x = UnionBaseMT $ liftIO $ UTSingle <$> x

instance (Show1 m, Show a, Show bool) => Show (UnionBaseM bool m a) where
  showsPrec i (UTSingle x) v = "UTSingle " ++ "(" ++ showsPrec i x v ++ ")"
  showsPrec i (UTIf cond mlr) v = "UTIf " ++ "(" ++ show cond ++ ") (" ++ showsPrec1 i mlr v ++ ")"

instance (Show1 m, Show a, Show bool) => Show (UnionBaseMT bool m a) where
  showsPrec i (UnionBaseMT x) = showsPrec1 i x

























newtype UnionBaseT2 bool m a =
  UnionBaseT2 { runUnionBaseT2 :: (m (Either a (bool, UnionBaseT2 bool m a, UnionBaseT2 bool m a))) }

instance (Show1 m, Show a, Show bool) => Show (UnionBaseT2 bool m a) where
  showsPrec i (UnionBaseT2 x) = showsPrec1 i x

instance Functor m => Functor (UnionBaseT2 bool m) where
  fmap f (UnionBaseT2 m) = UnionBaseT2 $ fmap (\case
     Left v1 -> Left $ f v1
     Right (cond, l, r) -> Right (cond, fmap f l, fmap f r)
    ) m

instance Applicative m => Applicative (UnionBaseT2 bool m) where
  pure x = UnionBaseT2 $ pure $ Left x
  (UnionBaseT2 f) <*> (UnionBaseT2 v) =
    UnionBaseT2 $ mk <$> f <*> v
    where
      mk (Left fv) (Left vv) = Left $ fv vv
      mk (Left fv) (Right (cond, l, r)) = Right (cond, fv <$> l, fv <$> r)
      mk (Right (cond, fl, fr)) r =
        Right (cond, fl <*> UnionBaseT2 (pure r), fr <*> UnionBaseT2 (pure r))

instance Monad m => Monad (UnionBaseT2 bool m) where
  (UnionBaseT2 m) >>= f = UnionBaseT2 $ do
    m1 <- m
    case m1 of
      Left v -> runUnionBaseT2 $ f v
      Right (cond, f1, f2) -> do
        l1 <- runUnionBaseT2 $ f1 >>= f
        l2 <- runUnionBaseT2 $ f2 >>= f
        return $ Right (cond, (UnionBaseT2 $ return l1), (UnionBaseT2 $ return l2))
        

newtype UnionBaseT bool m a = UnionBaseT { runUnionBaseT :: m (UnionBase bool a) }

instance (Show1 m, Show a, Show bool) => Show (UnionBaseT bool m a) where
  showsPrec i (UnionBaseT x) = showsPrec1 i x

ifT :: (SymBoolOp bool, Monad m) => bool -> UnionBaseT bool m a -> UnionBaseT bool m a -> UnionBaseT bool m a
ifT cond (UnionBaseT l) (UnionBaseT r) = UnionBaseT $ do
  l1 <- l
  r1 <- r
  return $ ifWithLeftMost False cond l1 r1

instance (SymBoolOp bool, Functor m) => Functor (UnionBaseT bool m) where
  fmap f (UnionBaseT x) = UnionBaseT $ go <$> x
    where
      go (Single v) = Single $ f v
      go (If _ _ cond l r) = ifWithLeftMost False cond (go l) (go r)

instance (SymBoolOp bool, Monad m) => Applicative (UnionBaseT bool m) where
  pure v = UnionBaseT $ pure $ Single v
  f <*> a = f >>= (\xf -> a >>= return . xf)

instance (SymBoolOp bool, Monad m) => Monad (UnionBaseT bool m) where
  (UnionBaseT v) >>= f = UnionBaseT $ do
    u <- v
    go u
    where
      go (Single s) = runUnionBaseT $ f s
      go (If _ _ cond l r) = do
        l1 <- go l
        r1 <- go r
        return $ ifWithLeftMost False cond l1 r1

instance (SymBoolOp bool) => MonadTrans (UnionBaseT bool) where
  lift = UnionBaseT . liftM Single

instance (SymBoolOp bool, MonadIO m) => MonadIO (UnionBaseT bool m) where
  liftIO = lift . liftIO

{-
-- |
-- >>> runUnionBaseT $ ((v (SSBool "a") >=> v (SSBool "b") ) >=> v (SSBool "c")) 0
{-If SSBool b
  (If SSBool c
    (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (If SSBool c (Single 0) (Single 1))))
    (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (If SSBool c (Single 0) (Single 1)))))
  (If SSBool c
    (If SSBool c
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 0))) 
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 1))))
    (If SSBool c 
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 0))) 
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 1)))))-}
-- >>> runUnionBaseT $ (v (SSBool "a") >=> (v (SSBool "b") >=> v (SSBool "c"))) 0
{-If SSBool c
  (If SSBool b
    (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (If SSBool c (Single 0) (Single 1))))
    (If SSBool c
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 0)))
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 1)))))
  (If SSBool b
    (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (If SSBool c (Single 0) (Single 1))))
    (If SSBool c
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 0)))
      (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 1)))))-}
v :: SBool -> Int -> UnionBaseT SBool (UnionBase SBool) Int
v s 0 = UnionBaseT $ Single $ ifWithLeftMost False s (return 0) (return 1)
v s 1 = UnionBaseT $ ifWithLeftMost False s (return $ Single 0) (return $ Single 1)


-- >>> runUnionBaseT2 $ ((v2 (SSBool "a") >=> v2 (SSBool "b") ) >=> v2 (SSBool "c")) 0
-- If SSBool b (If SSBool c (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 0))),Single (Right (SSBool c,Single (Left 0),Single (Left 1)))))) (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 1))),Single (Right (SSBool c,Single (Left 0),Single (Left 1))))))) (If SSBool c (If SSBool c (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 0))),Single (Left 0)))) (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 0))),Single (Left 1))))) (If SSBool c (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 1))),Single (Left 0)))) (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 1))),Single (Left 1))))))
-- >>> runUnionBaseT2 $ (v2 (SSBool "a") >=> (v2 (SSBool "b") >=> v2 (SSBool "c"))) 0
-- If SSBool c (If SSBool b (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 0))),Single (Right (SSBool c,Single (Left 0),Single (Left 1)))))) (If SSBool c (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 0))),Single (Left 0)))) (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 0))),Single (Left 1)))))) (If SSBool b (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 1))),Single (Right (SSBool c,Single (Left 0),Single (Left 1)))))) (If SSBool c (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 1))),Single (Left 0)))) (Single (Right (SSBool a,Single (Right (SSBool b,Single (Right (SSBool c,Single (Left 0),Single (Left 1))),Single (Left 1))),Single (Left 1))))))
v2 :: SBool -> Int -> UnionBaseT2 SBool (UnionBase SBool) Int
v2 s 0 = UnionBaseT2 $ Single $ Right (s, (return 0), (return 1))
v2 s 1 = UnionBaseT2 $ ifWithLeftMost False s (return $ Left 0) (return $ Left 1)


t :: UnionBaseT SBool IO Int
t = ifT (SSBool "a") (do
  liftIO $ print "a"
  return 1) (do
  liftIO $ print "b"
  return 1)


test1 :: UnionBaseT SBool IO Int
test1 = do
  r <- liftIO (newIORef 0)
  (ifT (SSBool "a") (next r) (next r) >> ifT (SSBool "b") (next r) (next r)) >> ifT (SSBool "c") (next r) (next r)

test2 :: UnionBaseT SBool IO Int
test2 = do
  r <- liftIO (newIORef 0)
  ifT (SSBool "a") (next r) (next r) >> (ifT (SSBool "b") (next r) (next r) >> ifT (SSBool "c") (next r) (next r))

test1M :: UnionBaseMT SBool IO Int
test1M = do
  r <- liftIO (newIORef 0)
  (ifMT (SSBool "a") (next r) (next r) >> ifMT (SSBool "b") (next r) (next r)) >> ifMT (SSBool "c") (next r) (next r)

test2M :: UnionBaseMT SBool IO Int
test2M = do
  r <- liftIO (newIORef 0)
  ifMT (SSBool "a") (next r) (next r) >> (ifMT (SSBool "b") (next r) (next r) >> ifMT (SSBool "c") (next r) (next r))


next :: MonadIO m => IORef Int -> m Int
next r = liftIO $ do  x <- readIORef r
                      writeIORef r (x+1)
                      return x


-- >>> runUnionBaseMTAll $ ((v3 (SSBool "a") >=> v3 (SSBool "b") ) >=> v3 (SSBool "c")) 0
-- If SSBool b (If SSBool c (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (If SSBool c (Single 0) (Single 1)))) (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (If SSBool c (Single 0) (Single 1))))) (If SSBool c (If SSBool c (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 0))) (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 0)))) (If SSBool c (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 1))) (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 1)))))
-- >>> runUnionBaseMTAll $ (v3 (SSBool "a") >=> (v3 (SSBool "b")  >=> v3 (SSBool "c"))) 0
-- If SSBool b (If SSBool c (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (If SSBool c (Single 0) (Single 1)))) (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (If SSBool c (Single 0) (Single 1))))) (If SSBool c (If SSBool c (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 0))) (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 0)))) (If SSBool c (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 0)) (Single 1))) (Single (If SSBool a (If SSBool b (If SSBool c (Single 0) (Single 1)) (Single 1)) (Single 1)))))
v3 :: SBool -> Int -> UnionBaseMT SBool (UnionBase SBool) Int
v3 s 0 = UnionBaseMT $ Single $ UTIf s (Single ((UTSingle 0), (UTSingle 1)))
v3 s 1 = UnionBaseMT $ ifWithLeftMost False s (Single $ UTSingle 0) (Single $ UTSingle 1)
v3 _ _ = undefined

-}

main :: IO ()
main = putStrLn "Hello world"