{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Grisette.Data.Class.Mergeable where
import Data.Typeable

data MergeStrategy bool a where
  SimpleStrategy :: (bool -> a -> a -> a) -> MergeStrategy bool a
  OrderedStrategy ::
    (Ord idx, Typeable idx, Show idx) =>
    (a -> idx) ->
    (idx -> MergeStrategy bool a) ->
    MergeStrategy bool a
  NoStrategy :: MergeStrategy bool a

class Mergeable' bool f where
  mergeStrategy' :: MergeStrategy bool (f a)

class Mergeable bool a where
  mergeStrategy :: MergeStrategy bool a
