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

type Exception raw = raw

assertWithException :: Q Exp
assertWithException = [|assertWithException' |]

assertWithException' ::
  forall exceptT raw.
  (MonadError (Exception raw) (exceptT (Exception raw) UnionM), UnionMOp SymBool (exceptT (Exception raw) UnionM)) =>
  raw ->
  SymBool ->
  exceptT (Exception raw) UnionM ()
assertWithException' ex x = mrgGuard x (return ()) (throwError ex)
