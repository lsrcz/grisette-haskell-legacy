{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Exception where

import Control.Monad.Except
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.SymPrim
import Language.Haskell.TH

type Exception raw = raw

assertWithException :: Q Exp
assertWithException = [|assertWithException'|]

assertWithException' ::
  forall exceptT raw.
  (MonadError (Exception raw) (exceptT (Exception raw) UnionM), UnionMOp SymBool (exceptT (Exception raw) UnionM)) =>
  raw ->
  SymBool ->
  exceptT (Exception raw) UnionM ()
assertWithException' ex x = mrgGuard x (return ()) (throwError ex)
