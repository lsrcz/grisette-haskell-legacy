{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Control.Carrier.Reader where

import Control.Carrier.Reader
import Grisette.Core

instance
  ( SymBoolOp bool,
    Mergeable1 bool m,
    Mergeable bool a
  ) =>
  Mergeable bool (ReaderC r m a)
  where
  mergingStrategy = mergingStrategy1

instance
  ( SymBoolOp bool,
    Mergeable1 bool m
  ) =>
  Mergeable1 bool (ReaderC r m)
  where
  liftMergingStrategy ms =
    wrapStrategy (liftMergingStrategy (liftMergingStrategy ms)) ReaderC (\(ReaderC rt) -> rt)

instance
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool a
  ) =>
  SimpleMergeable bool (ReaderC r m a)
  where
  mrgIte = mrgIf

instance
  ( SymBoolOp bool,
    UnionLike bool m
  ) =>
  SimpleMergeable1 bool (ReaderC r m)
  where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy

instance
  ( SymBoolOp bool,
    UnionLike bool m
  ) =>
  UnionLike bool (ReaderC r m)
  where
  mergeWithStrategy ms (ReaderC f) = ReaderC $ \r -> mergeWithStrategy ms (f r)
  mrgIfWithStrategy ms cond (ReaderC l) (ReaderC r) = ReaderC $
    \v -> mrgIfWithStrategy ms cond (l v) (r v)
  mrgSingleWithStrategy ms a = ReaderC $ \_ -> mrgSingleWithStrategy ms a
  single a = ReaderC $ \_ -> single a
  unionIf cond (ReaderC l) (ReaderC r) = ReaderC $ \v -> unionIf cond (l v) (r v)

mrgRunReader ::
  ( SymBoolOp bool,
    UnionLike bool m,
    Mergeable bool a
  ) =>
  r ->
  ReaderC r m a ->
  m a
mrgRunReader r (ReaderC f) = merge $ f r
