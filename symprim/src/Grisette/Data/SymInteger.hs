{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.SymInteger
  ( SymInteger,
  )
where

import Control.Monad.Except
import Grisette.Control.Monad
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Integer
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.SymBool ()
import Grisette.Data.SymPrim

type SymInteger = Sym Integer

instance Show (Sym Integer) where
  show (Sym t) = pformat t

instance SEq (Sym Bool) (Sym Integer) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance LinearArithOp (Sym Integer) where
  (Sym l) +~ (Sym r) = Sym $ addi l r
  (Sym l) -~ (Sym r) = Sym $ minusi l r
  negs (Sym v) = Sym $ uminusi v

instance TimesOp (Sym Integer) where
  (Sym l) *~ (Sym r) = Sym $ timesi l r

instance SymConcView Integer where
  symConcView (Sym (IntegerConcTerm t)) = Just t
  symConcView _ = Nothing

instance SignedDivMod (Sym Bool) (Sym Integer) where
  divs (Sym l) rs@(Sym r) =
    withSimpleMergeableU @(Sym Bool) $
      mrgIf @(Sym Bool)
        (rs ==~ conc 0)
        (throwError $ transformError DivByZeroError)
        (mrgReturn $ Sym $ divi l r)
  mods (Sym l) rs@(Sym r) =
    withSimpleMergeableU @(Sym Bool) $
      mrgIf @(Sym Bool)
        (rs ==~ conc 0)
        (throwError $ transformError DivByZeroError)
        (mrgReturn $ Sym $ modi l r)

instance SymIntegerOp (Sym Bool) (Sym Integer)
