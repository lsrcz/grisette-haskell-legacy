{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Grisette.Lib.Control.Carrier.Lift where
import Grisette.Core
import Control.Carrier.Lift

instance (UnionLike bool m, Mergeable bool a) => Mergeable bool (LiftC m a) where
  mergeStrategy = wrapMergeStrategy mergeStrategy1 LiftC (\(LiftC m) -> m)

instance (UnionLike bool m) => Mergeable1 bool (LiftC m) where
  liftMergeStrategy ms = wrapMergeStrategy (liftMergeStrategy ms) LiftC (\(LiftC m) -> m)

instance (UnionLike bool m, Mergeable bool a) => SimpleMergeable bool (LiftC m a) where
  mrgIte = mrgIf

instance (UnionLike bool m) => SimpleMergeable1 bool (LiftC m) where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy

instance (UnionLike bool m) => UnionLike bool (LiftC m) where
  mergeWithStrategy s (LiftC v) = LiftC $ mergeWithStrategy s v
  mrgIfWithStrategy s cond (LiftC l) (LiftC r) = LiftC $ mrgIfWithStrategy s cond l r
  mrgSingleWithStrategy s v = LiftC $ mrgSingleWithStrategy s v
  single x = LiftC $ single x
  unionIf cond (LiftC l) (LiftC r) = LiftC $ unionIf cond l r

mrgRunM :: (UnionLike bool m, Mergeable bool a) => LiftC m a -> m a
mrgRunM = merge . runM
