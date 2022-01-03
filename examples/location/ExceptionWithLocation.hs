{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module ExceptionWithLocation where

import Control.Monad.Except
import qualified Data.ByteString.UTF8 as B
import Debug.Trace.LocationTH (__LOCATION__)
import GHC.Generics
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.SymPrim
import Language.Haskell.TH

data Exception raw = ExceptionWithLocation raw B.ByteString deriving (Show, Generic)

instance (SymBoolOp bool, Mergeable bool raw) => Mergeable bool (Exception raw)

exceptWithLocation :: Q Exp
exceptWithLocation = [|\e -> ExceptionWithLocation e (B.fromString $__LOCATION__)|]

assertWithException :: Q Exp
assertWithException = [|assertWithException' (B.fromString $__LOCATION__)|]

assertWithException' ::
  forall exceptT raw.
  (MonadError (Exception raw) (exceptT (Exception raw) UnionM), UnionMOp SymBool (exceptT (Exception raw) UnionM)) =>
  B.ByteString ->
  raw ->
  SymBool ->
  exceptT (Exception raw) UnionM ()
assertWithException' loc ex x = mrgGuard x (return ()) (throwError $ ExceptionWithLocation ex loc)
