{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Data.List where

import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Control.Exception

(!!~) ::
  ( SymBoolOp bool,
    SymIntegerOp bool integer,
    UnionMOp bool uf,
    MonadError e uf,
    TransformError ArrayException e,
    Mergeable bool a
  ) =>
  [a] ->
  integer ->
  uf a
l !!~ p = go l p 0
  where
    go [] _ _ = throwError $ transformError (IndexOutOfBounds "!!~")
    go (x : xs) p1 i = mrgGuard (p1 ==~ i) (mrgSingle x) (go xs p1 $ i + 1)

symFilter :: (SymBoolOp bool, UnionMOp bool u, Mergeable bool a, Monad u) => (a -> bool) -> [a] -> u [a]
symFilter f = go
  where
    go [] = mrgSingle []
    go (x:xs) = do
      r <- go xs
      mrgGuard (f x) (mrgSingle (x : r)) (mrgSingle r)

