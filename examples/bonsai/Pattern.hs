module Pattern where

import BonsaiTree
import Control.Monad.Except
-- import qualified Data.ByteString as B
import GHC.TypeLits
import Grisette.SymPrim.Term
-- import qualified Data.ByteString.Char8 as C

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

data PatternHandler m e t
  = PatternHandler0 (Pattern m 0) (ExceptT e UnionM t)
  | PatternHandler1 (Pattern m 1) (UnionM (BonsaiTree m) -> ExceptT e UnionM t)
  | PatternHandler2
      (Pattern m 2)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )
  | PatternHandler3
      (Pattern m 3)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )
  | PatternHandler4
      (Pattern m 4)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )
  | PatternHandler5
      (Pattern m 5)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )

applyHandler :: [UnionM (BonsaiTree m)] -> PatternHandler m e t -> ExceptT e UnionM t
applyHandler [] (PatternHandler0 _ h) = h
applyHandler [a] (PatternHandler1 _ h) = h a
applyHandler [a, b] (PatternHandler2 _ h) = h a b
applyHandler [a, b, c] (PatternHandler3 _ h) = h a b c
applyHandler [a, b, c, d] (PatternHandler4 _ h) = h a b c d
applyHandler [a, b, c, d, e] (PatternHandler5 _ h) = h a b c d e
applyHandler _ _ = undefined

class GetPatternHandler n m e f t | n m e t -> f where
  (==>) :: Pattern m n -> f -> PatternHandler m e t

instance GetPatternHandler 0 m e (ExceptT e UnionM t) t where
  (==>) = PatternHandler0

instance GetPatternHandler 1 m e (UnionM (BonsaiTree m) -> ExceptT e UnionM t) t where
  (==>) = PatternHandler1

instance
  GetPatternHandler
    2
    m
    e
    ( UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      ExceptT e UnionM t
    )
    t
  where
  (==>) = PatternHandler2

instance
  GetPatternHandler
    3
    m
    e
    ( UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      ExceptT e UnionM t
    )
    t
  where
  (==>) = PatternHandler3

instance
  GetPatternHandler
    4
    m
    e
    ( UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      ExceptT e UnionM t
    )
    t
  where
  (==>) = PatternHandler4

instance
  GetPatternHandler
    5
    m
    e
    ( UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      UnionM (BonsaiTree m) ->
      ExceptT e UnionM t
    )
    t
  where
  (==>) = PatternHandler5

