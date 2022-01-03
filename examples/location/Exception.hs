{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Exception where
import Language.Haskell.TH
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.SymPrim
import Grisette.Control.Monad.UnionM
import Control.Monad.Except
import RawException

type Exception = RawException

assertWithException :: Q Exp
assertWithException = [|assertWithException' |]

assertWithException' ::
  forall exceptT.
  (MonadError Exception (exceptT Exception UnionM), UnionMOp SymBool (exceptT Exception UnionM)) =>
  RawException ->
  SymBool ->
  exceptT Exception UnionM ()
assertWithException' ex x = mrgGuard x (return ()) (throwError ex)
