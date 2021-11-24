{-# LANGUAGE MultiParamTypeClasses #-}

module Grisette.Data.Class.Error (TransformError (..)) where

class TransformError from to where
  transformError :: from -> to