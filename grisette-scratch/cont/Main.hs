{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.Cont
import Debug.Trace
import GHC.Generics
import Grisette

a :: UnionM Integer
a = mrgIf "a" 1 2

f1 :: Integer -> UnionM Integer
f1 x = mrgIf "b" (mrgReturn x) (mrgReturn $ x + 1)

-- |
-- >>> a >>= f1 >>= f1
-- >>> a >>= (\x -> f1 x >>= f1)
-- UMrg (If (&& a b) (Single 1) (If b (Single 2) (If (|| a b) (Single 3) (Single 4))))
-- UMrg (If (&& a b) (Single 1) (If (&& (! a) b) (Single 2) (If a (Single 3) (Single 4))))

-- | >>> runContT (mrgIf (ssymb "a") (return 1) (return 1) >>= return) (\x -> mrgReturn x) :: UnionM Integer
-- UMrg (Single 1)
{-
mrgResetT ::
  ( Monad m,
    UnionLike bool m,
    Mergeable bool a
  ) =>
  ContT a m a ->
  ContT a1 m a
mrgResetT m = lift $ runContT m mrgReturn
-}

newtype X = X Int
  deriving (Show, Eq, Generic)
  deriving (Mergeable bool) via (Default X)

rid :: Int -> ContT r UnionM Int
rid i = ContT $ \c -> c i

rt :: (Mergeable SymBool r) => SymBool -> Int -> ContT r UnionM Int
rt x i = mrgIf x (rid i) (rid $ i + 1)

main :: IO ()
main = do
  print $ runContT (rt "a" 1 >>= rt "b" >>= rt "c") (\x -> trace (show x) $ mrgReturn x)
  print $ runContT (mrgResetT (rt "a" 1 >>= rt "b") >>= rt "c") (\x -> trace (show x) $ mrgReturn x)
