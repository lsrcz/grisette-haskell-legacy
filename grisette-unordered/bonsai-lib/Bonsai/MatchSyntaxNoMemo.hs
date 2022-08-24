module Bonsai.MatchSyntaxNoMemo where

import Bonsai.BonsaiTree
import Bonsai.SyntaxSpec
import qualified Data.ByteString as B
import qualified Data.HashSet as S
import GHC.TypeLits
import Grisette

matchSyntax ::
  (KnownNat n, 1 <= n) =>
  OptimSyntaxSpec n ->
  (Rule -> BonsaiTree (SymWordN n) -> SymBool) ->
  BonsaiTree (SymWordN n) ->
  B.ByteString ->
  SymBool
matchSyntax stx fR tree sym = case getRules stx sym of
  Nothing -> conc False
  Just rus -> foldl (\acc rule -> acc ||~ fR rule tree) (conc False) rus
{-# INLINE matchSyntax #-}

matchRule ::
  (KnownNat n, 1 <= n) =>
  OptimSyntaxSpec n ->
  (BonsaiTree (SymWordN n) -> B.ByteString -> SymBool) ->
  (Rule -> BonsaiTree (SymWordN n) -> SymBool) ->
  Rule ->
  BonsaiTree (SymWordN n) ->
  SymBool
matchRule stx fS fR rule tree = case (tree, rule) of
  (_, SymRule sym) | sym `S.member` nonTerminals stx -> fS tree sym
  (BonsaiNode left right, PairRule first second) ->
    getSingle (fR first <$> left)
      &&~ getSingle (fR second <$> right)
  (BonsaiLeaf sym, SymRule sym1) -> Just sym ==~ (conc <$> terminalToBV stx sym1)
  _ -> conc False
{-# INLINE matchRule #-}
