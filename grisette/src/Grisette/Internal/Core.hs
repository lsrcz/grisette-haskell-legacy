{-# LANGUAGE PatternSynonyms #-}

module Grisette.Internal.Core
  ( UnionBase (..),
    guardWithLeftMost,
    guardWithStrategy,
    fullReconstruct,
    UnionMBase (..),
    underlyingUnion,
    isMerged,
  )
where

import Grisette.Control.Monad.UnionMBase
import Grisette.Data.UnionBase
