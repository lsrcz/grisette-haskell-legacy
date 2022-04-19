module Grisette.Data.List
  ( (!!~),
    symFilter,
    symTake,
    symDrop,
  )
where

import Control.Exception
import Control.Monad.Except
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Control.Monad
import Grisette.Data.Class.SOrd

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

symTake :: (SymBoolOp bool, MonadUnion bool u, Mergeable bool a, SymIntegerOp bool integer) => integer -> [a] -> u [a]
symTake _ [] = mrgReturn []
symTake x (v:vs) = mrgIf (x <=~ 0) (mrgReturn []) (mrgFmap (v:) $ symTake (x - 1) vs)

symDrop :: (SymBoolOp bool, MonadUnion bool u, Mergeable bool a, SymIntegerOp bool integer) => integer -> [a] -> u [a]
symDrop _ [] = mrgReturn []
symDrop x r@(_:vs) = mrgIf (x <=~ 0) (mrgReturn r) (symDrop (x - 1) vs)