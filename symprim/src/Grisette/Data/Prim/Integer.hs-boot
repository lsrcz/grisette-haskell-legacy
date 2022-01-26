{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Data.Prim.Integer where
import Grisette.Data.Prim.InternedTerm

integerConcTermView :: forall a. Term a -> Maybe Integer

