{-# LANGUAGE GADTs #-}
module Grisette.Data.Prim.Num where

data AddNum x where
  AddNum :: (Num x) => AddNum x