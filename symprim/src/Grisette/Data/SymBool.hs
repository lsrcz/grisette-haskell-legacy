{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Data.SymBool
  ( SymBool,
  )
where

import Data.Hashable
import Grisette.Data.Class.Bool
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.SymPrim

type SymBool = Sym Bool

instance Show (Sym Bool) where
  show (Sym t) = pformat t

instance SEq (Sym Bool) (Sym Bool) where
  (Sym l) ==~ (Sym r) = Sym $ eqterm l r

instance LogicalOp (Sym Bool) where
  (Sym l) ||~ (Sym r) = Sym $ orb l r
  (Sym l) &&~ (Sym r) = Sym $ andb l r
  nots (Sym v) = Sym $ notb v

instance Eq (Sym Bool) where
  (Sym l) == (Sym r) = l == r

instance Hashable (Sym Bool) where
  hashWithSalt s (Sym v) = s `hashWithSalt` v

instance SymBoolOp (Sym Bool)

instance SymConcView Bool where
  symConcView (Sym (BoolConcTerm t)) = Just t
  symConcView _ = Nothing
