module Grisette.Control.Monad.Trans where
import Grisette.Control.Monad.Union.MonadUnion
import Control.Monad.Trans
import Grisette.Control.Monad.Union.Mergeable

mrgLift :: (MonadTrans t, MonadUnion bool (t m), MonadUnion bool m, Mergeable bool a) => m a -> t m a
mrgLift = merge . lift
