module MatchSyntax where

import BonsaiTree
import qualified Data.ByteString as B
import qualified Data.HashSet as S
import GHC.TypeLits
import Grisette.Core
import Grisette.SymPrim.Term
import SyntaxSpec

matchSyntax ::
  (KnownNat n, 1 <= n) =>
  OptimSyntaxSpec n ->
  (Rule -> BonsaiTree (SymUnsignedBV n) -> SymBool) ->
  BonsaiTree (SymUnsignedBV n) ->
  B.ByteString ->
  SymBool
matchSyntax stx fR = htmemo2 $ \tree sym -> case getRules stx sym of
  Nothing -> conc False
  Just rus -> foldl (\acc rule -> acc ||~ fR rule tree) (conc False) rus

matchRule ::
  (KnownNat n, 1 <= n) =>
  OptimSyntaxSpec n ->
  (BonsaiTree (SymUnsignedBV n) -> B.ByteString -> SymBool) ->
  (Rule -> BonsaiTree (SymUnsignedBV n) -> SymBool) ->
  Rule ->
  BonsaiTree (SymUnsignedBV n) ->
  SymBool
matchRule stx fS fR = htmemo2 $ \rule tree -> case (tree, rule) of
  (_, SymRule sym) | sym `S.member` nonTerminals stx -> fS tree sym
  (BonsaiNode left right, PairRule first second) ->
    getSingle (fR first <$> left)
      &&~ getSingle (fR second <$> right)
  (BonsaiLeaf sym, SymRule sym1) -> Just sym ==~ (conc <$> terminalToBV stx sym1)
  _ -> conc False
