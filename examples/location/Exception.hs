{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}

module Exception where

import Control.Monad.Except
import Grisette.Data.Class.SimpleMergeable
import Language.Haskell.TH
import Grisette.Data.Class.Bool

type Exception raw = raw

assertWithException :: Q Exp
assertWithException = [|assertWithException'|]

assertWithException' ::
  forall bool raw eu.
  (SymBoolOp bool, MonadError (Exception raw) eu, UnionMOp bool eu) =>
  raw ->
  bool ->
  eu ()
assertWithException' ex x = mrgGuard x (return ()) (throwError ex)
