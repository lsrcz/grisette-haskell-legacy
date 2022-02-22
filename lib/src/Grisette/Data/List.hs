module Grisette.Data.List
  ( (!!~),
    symFilter,
  )
where

import Control.Exception
import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Control.Monad

(!!~) ::
  ( SymBoolOp bool,
    SymIntegerOp bool integer,
    MonadUnion bool uf,
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
    go (x : xs) p1 i = mrgIf (p1 ==~ i) (mrgReturn x) (go xs p1 $ i + 1)

symFilter :: (SymBoolOp bool, MonadUnion bool u, Mergeable bool a) => (a -> bool) -> [a] -> u [a]
symFilter f = go
  where
    go [] = mrgReturn []
    go (x : xs) = do
      r <- go xs
      mrgIf (f x) (mrgReturn (x : r)) (mrgReturn r)
