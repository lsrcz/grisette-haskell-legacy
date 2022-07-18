{-# LANGUAGE PolyKinds #-}

module Bonsai.Pattern where

import Bonsai.BonsaiTree
import Control.Monad.Except
import GHC.TypeLits
import Grisette

data Pattern a n where
  LiteralPattern :: a -> Pattern a 0
  PlaceHolder :: Pattern a 1
  PairPattern :: Pattern a n -> Pattern a m -> Pattern a (n + m)

instance (Show x) => Show (Pattern x n) where
  show (LiteralPattern x) = show x
  show PlaceHolder = "_"
  show (PairPattern l r) = "(" ++ show l ++ ", " ++ show r ++ ")"

(*=) :: Pattern a n -> Pattern a m -> Pattern a (n + m)
(*=) = PairPattern

literal :: a -> Pattern a 0
literal = LiteralPattern

placeHolder :: Pattern a 1
placeHolder = PlaceHolder

type HandlerType0 m e t = ExceptT e UnionM t

type HandlerType1 m e t = UnionM (BonsaiTree m) -> HandlerType0 m e t

type HandlerType2 m e t = UnionM (BonsaiTree m) -> HandlerType1 m e t

type HandlerType3 m e t = UnionM (BonsaiTree m) -> HandlerType2 m e t

type HandlerType4 m e t = UnionM (BonsaiTree m) -> HandlerType3 m e t

type HandlerType5 m e t = UnionM (BonsaiTree m) -> HandlerType4 m e t

data PatternHandler m e t
  = PatternHandler0 (Pattern m 0) (HandlerType0 m e t)
  | PatternHandler1 (Pattern m 1) (HandlerType1 m e t)
  | PatternHandler2 (Pattern m 2) (HandlerType2 m e t)
  | PatternHandler3 (Pattern m 3) (HandlerType3 m e t)
  | PatternHandler4 (Pattern m 4) (HandlerType4 m e t)
  | PatternHandler5 (Pattern m 5) (HandlerType5 m e t)

applyHandler :: [UnionM (BonsaiTree m)] -> PatternHandler m e t -> ExceptT e UnionM t
applyHandler [] (PatternHandler0 _ h) = h
applyHandler [a] (PatternHandler1 _ h) = h a
applyHandler [a, b] (PatternHandler2 _ h) = h a b
applyHandler [a, b, c] (PatternHandler3 _ h) = h a b c
applyHandler [a, b, c, d] (PatternHandler4 _ h) = h a b c d
applyHandler [a, b, c, d, e] (PatternHandler5 _ h) = h a b c d e
applyHandler _ _ = undefined
{-# INLINE applyHandler #-}

class GetPatternHandler n m e f t | n m e t -> f where
  (==>) :: Pattern m n -> f -> PatternHandler m e t

instance GetPatternHandler 0 m e (HandlerType0 m e t) t where
  (==>) = PatternHandler0

instance GetPatternHandler 1 m e (HandlerType1 m e t) t where
  (==>) = PatternHandler1

instance GetPatternHandler 2 m e (HandlerType2 m e t) t where
  (==>) = PatternHandler2

instance GetPatternHandler 3 m e (HandlerType3 m e t) t where
  (==>) = PatternHandler3

instance GetPatternHandler 4 m e (HandlerType4 m e t) t where
  (==>) = PatternHandler4

instance GetPatternHandler 5 m e (HandlerType5 m e t) t where
  (==>) = PatternHandler5
