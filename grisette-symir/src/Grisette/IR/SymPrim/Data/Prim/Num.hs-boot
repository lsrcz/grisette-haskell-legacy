{-# LANGUAGE GADTs #-}

module Grisette.IR.SymPrim.Data.Prim.Num where

data AddNum x where
  AddNum :: (Num x) => AddNum x