module Pattern where

import BonsaiTree
import Control.Monad.Except
import qualified Data.ByteString as B
import GHC.TypeLits
import Grisette.SymPrim.Term

data Pattern n where
  LiteralPattern :: B.ByteString -> Pattern 0
  PlaceHolder :: Pattern 1
  PairPattern :: Pattern n -> Pattern m -> Pattern (n + m)

(*=) :: Pattern n -> Pattern m -> Pattern (n + m)
(*=) = PairPattern

literal :: B.ByteString -> Pattern 0
literal = LiteralPattern

placeHolder :: Pattern 1 
placeHolder = PlaceHolder

data PatternHandler m e t
  = PatternHandler0 (Pattern 0) (ExceptT e UnionM t)
  | PatternHandler1 (Pattern 1) (UnionM (BonsaiTree m) -> ExceptT e UnionM t)
  | PatternHandler2
      (Pattern 2)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )
  | PatternHandler3
      (Pattern 3)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )
  | PatternHandler4
      (Pattern 4)
      ( UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        UnionM (BonsaiTree m) ->
        ExceptT e UnionM t
      )
  | PatternHandler5
      (Pattern 5)
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
  (==>) :: Pattern n -> f -> PatternHandler m e t

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

