{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Grisette.Lib.Text.Megaparsec where

import Control.Monad.Trans
import Grisette.Core
import Text.Megaparsec
import Text.Megaparsec.Internal

instance (Stream s, MonadGenSymFresh m) => MonadGenSymFresh (ParsecT e s m) where
  nextGenSymIndex = lift nextGenSymIndex
  getGenSymIdent = lift getGenSymIdent

instance (SymBoolOp bool, UnionLike bool m) => Mergeable bool (ParsecT e s m a) where
  mergingStrategy = SimpleStrategy unionIf

instance (SymBoolOp bool, UnionLike bool m) => Mergeable1 bool (ParsecT e s m) where
  liftMergingStrategy _ = SimpleStrategy unionIf

instance (SymBoolOp bool, UnionLike bool m) => SimpleMergeable bool (ParsecT e s m a) where
  mrgIte = unionIf

instance (SymBoolOp bool, UnionLike bool m) => SimpleMergeable1 bool (ParsecT e s m) where
  liftMrgIte _ = unionIf

instance (SymBoolOp bool, UnionLike bool m) => UnionLike bool (ParsecT e s m) where
  single x = ParsecT $ \s _ _ eok _ -> eok x s mempty
  unionIf cond (ParsecT l) (ParsecT r) =
    ParsecT $ \s cok cerr eok eerr -> unionIf cond (l s cok cerr eok eerr) (r s cok cerr eok eerr)
  mergeWithStrategy _ = id
