{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Grisette

symFilter1 :: forall bool u a. (SymBoolOp bool, MonadUnion bool u, Mergeable bool a) => (a -> bool) -> [a] -> u [a]
symFilter1 f l = go l (mrgReturn [])
  where
    go :: [a] -> u [a] -> u [a]
    go [] r = mrgFmap reverse r
    go (x : xs) r = do
      res <- mrgReturnWithStrategy mergeStrategy1 $ mrgIf @bool @u @[a] (f x) (mrgFmap (x:) r) r
      go xs res


main :: IO()
main = do
  print $ (symFilter id [ssymb "a", ssymb "b", ssymb "c"] :: UnionM [SymBool])
  print $ do
    x1 <- (symFilter1 ((ssymb "f" :: Bool =~> Bool) #) [ssymb "a", ssymb "b"] :: UnionM [SymBool])
    symFilter1 ((ssymb "f1" :: Bool =~> Bool) #) x1 :: UnionM [SymBool]
  print $ do
    l <- mrgIf (ssymb "c") (mrgReturn [ssymb "a"]) (mrgReturn [ssymb "a", ssymb "b"])
    (symFilter1 id l :: UnionM [SymBool])
  print $ do
    l <- mrgIf (ssymb "d") (mrgIf (ssymb "e") (mrgReturn [ssymb "a"]) (mrgReturn [ssymb "a", ssymb "b"])) (mrgReturn [ssymb "a", ssymb "b", ssymb "c"])
    (symFilter1 id l :: UnionM [SymBool])
