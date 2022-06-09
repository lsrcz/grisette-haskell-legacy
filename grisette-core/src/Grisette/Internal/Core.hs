{-# LANGUAGE PatternSynonyms #-}

module Grisette.Internal.Core
  ( UnionBase (..),
    ifWithLeftMost,
    ifWithStrategy,
    fullReconstruct,
    UnionMBase (..),
    underlyingUnion,
    isMerged,
  )
where

import Grisette.Control.Monad.UnionMBase
import Grisette.Data.UnionBase
