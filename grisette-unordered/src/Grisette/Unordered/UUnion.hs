{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Grisette.Unordered.UUnion where

import Control.DeepSeq
import Data.Functor.Classes
import qualified Data.Map.Strict as M
import GHC.Generics
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.SimpleMergeable
import Language.Haskell.TH.Syntax
import Grisette.Core.Data.Class.PrimWrapper
import Data.Bifunctor
import Data.Hashable

newtype UUnionBase b a = UUnionBase [(b, a)]
  deriving (Generic, Eq, Lift, Generic1)

instance Eq b => Eq1 (UUnionBase b) where
  liftEq e (UUnionBase l) (UUnionBase r) = and $ zipWith (liftEq e) l r

instance (NFData b, NFData a) => NFData (UUnionBase b a) where
  rnf = rnf1

instance (NFData b) => NFData1 (UUnionBase b) where
  liftRnf = liftRnf2 rnf

instance NFData2 UUnionBase where
  liftRnf2 _b _a (UUnionBase []) = ()
  liftRnf2 _b _a (UUnionBase ((b, a) : t)) = _b b `seq` _a a `seq` liftRnf2 _b _a (UUnionBase t)

instance (SymBoolOp bool, Mergeable bool a) => Mergeable bool (UUnionBase bool a) where
  mergingStrategy = SimpleStrategy $ mrgIfWithStrategy mergingStrategy

instance SymBoolOp bool => Mergeable1 bool (UUnionBase bool) where
  liftMergingStrategy ms = SimpleStrategy $ mrgIfWithStrategy ms

instance (SymBoolOp bool, Mergeable bool a) => SimpleMergeable bool (UUnionBase bool a) where
  mrgIte = mrgIf

instance SymBoolOp bool => SimpleMergeable1 bool (UUnionBase bool) where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance SymBoolOp bool => UnionLike bool (UUnionBase bool) where
  mergeWithStrategy = fullReconstructUnordered
  single v = UUnionBase [(conc True, v)]
  unionIf cond (UUnionBase l) (UUnionBase r) = UUnionBase $ fmap (first (cond &&~)) l ++ fmap (first (nots cond &&~)) r
  mrgIfWithStrategy s cond l r = fullReconstructUnordered s $ unionIf cond l r
  mrgSingleWithStrategy _ = single

fullReconstructUnordered :: (SymBoolOp bool) => MergingStrategy bool a -> UUnionBase bool a -> UUnionBase bool a
fullReconstructUnordered s (UUnionBase l) = UUnionBase $ reconstruct $ partitioned
  where
    partition [] m = m
    partition ((b, a) : xs) m = case resolveStrategy s a of
      (idxs, subs) ->
        M.alter
          ( \case
              Nothing -> Just [(b, a, subs)]
              Just ls -> Just $ (b, a, subs) : ls
          )
          idxs
          (partition xs m)
    partitioned = fmap snd . M.toList $ partition l M.empty
    reconstruct [] = []
    reconstruct (x : xss) = go x xss
      where
        go [] _ = undefined
        go [(b, a, _)] xs = (b, a) : reconstruct xs
        go ((b, a, NoStrategy) : baxs) xs = (b, a) : reconstruct (baxs : xs)
        go ((b, a, SimpleStrategy m) : (b1, a1, _) : baxs) xs =
          reconstruct (((b ||~ b1, m b a a1, SimpleStrategy m) : baxs) : xs)
        go (_ : _) _ = undefined

instance (Show b) => Show1 (UUnionBase b) where
  liftShowsPrec sp sl i (UUnionBase l) = showParen (i > 10) $ showString "UUnionBase [" . liftShowList2 showsPrec showList sp sl l . showString "]"

instance (Show b, Show a) => Show (UUnionBase b a) where
  showsPrec = showsPrec1

instance (Hashable b, Hashable a) => Hashable (UUnionBase b a) where
  s `hashWithSalt` (UUnionBase l) = s `hashWithSalt` l

instance SymBoolOp bool => UnionPrjOp bool (UUnionBase bool) where
  singleView (UUnionBase [(_,a)]) = Just a
  singleView _ = Nothing
  ifView _ = undefined
  leftMost _ = undefined

  