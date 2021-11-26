{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Data.SymTabularFunc where
import Grisette.Data.TabularFunc
import Grisette.Data.SymPrim
import Grisette.Data.Class.FiniteFunction
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.Class.PrimWrapper

newtype (a =~> b) = SymTabularFunc (Term (a =-> b))

instance (SymPrimType a, SymPrimType b) => SymPrimType (a =-> b) where
  type SymPrim (a =-> b) = a =~> b
  underlyingTerm (SymTabularFunc v) = v
  wrapTerm = SymTabularFunc

instance (SupportedPrim a, SupportedPrim b, SymPrimType a, SymPrimType b) => FiniteFunction (a =~> b)  where
  type Arg (a =~> b) = SymPrim a
  type Ret (a =~> b) = SymPrim b
  runFunc (SymTabularFunc f) t = wrapTerm $ applyf f (underlyingTerm t)

instance (SupportedPrim a, SupportedPrim b) => PrimWrapper (a =~> b) (a =-> b) where
  conc = SymTabularFunc . concTerm
  concView (SymTabularFunc (TabularFuncConcTerm t)) = Just t
  concView _ = Nothing
  ssymb = SymTabularFunc . ssymbTerm
  isymb i str = SymTabularFunc $ isymbTerm i str
