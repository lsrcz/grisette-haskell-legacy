module Grisette.Data.Class.Utils.CConst (CConst (..)) where

import Data.Constraint

-- | Helper to carry a constraint with a constant functor.
data CConst (c :: Constraint) a b = c => CConst {unCConst :: a}
