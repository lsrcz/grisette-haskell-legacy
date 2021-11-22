{-# LANGUAGE MultiParamTypeClasses #-}
module Grisette.Data.Class.Error where

class TransformError from to where
  transformError :: from -> to