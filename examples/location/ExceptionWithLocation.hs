{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module ExceptionWithLocation where

import Control.Monad.Except
import Debug.Trace.LocationTH (__LOCATION__)
import qualified RawException as E
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.SymPrim
import Language.Haskell.TH
import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import qualified Data.ByteString.UTF8 as B

data Exception = ExceptionWithLocation E.RawException B.ByteString deriving (Show, Generic)

instance (SymBoolOp bool) => Mergeable bool Exception where

exceptWithLocation :: Q Exp
exceptWithLocation = [|\e -> ExceptionWithLocation e (B.fromString $__LOCATION__)|]

assertWithException :: Q Exp
assertWithException = [|assertWithException' (B.fromString $__LOCATION__)|]

assertWithException' ::
  forall exceptT.
  (MonadError Exception (exceptT Exception UnionM), UnionMOp SymBool (exceptT Exception UnionM)) =>
  B.ByteString ->
  E.RawException ->
  SymBool ->
  exceptT Exception UnionM ()
assertWithException' loc ex x = mrgGuard x (return ()) (throwError $ ExceptionWithLocation ex loc)
