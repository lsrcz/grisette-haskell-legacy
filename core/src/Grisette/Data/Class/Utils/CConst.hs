module Grisette.Data.Class.Utils.CConst (CConst (..)) where

import Data.Constraint

data CConst (c :: Constraint) a b = c => CConst {unCConst :: a}
