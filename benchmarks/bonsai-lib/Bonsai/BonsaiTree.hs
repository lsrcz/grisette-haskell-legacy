{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Bonsai.BonsaiTree where

import Control.DeepSeq
import Data.BitVector.Sized.Unsigned
import qualified Data.ByteString as B
import Data.Hashable
import Data.Maybe
import Data.MemoTrie
import Generics.Deriving
import GHC.TypeNats
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Bonsai.SyntaxSpec

data ConcBonsaiTree leaf
  = ConcBonsaiLeaf leaf
  | ConcBonsaiNode (ConcBonsaiTree leaf) (ConcBonsaiTree leaf)
  deriving (Show, Generic)

data BonsaiTree leaf
  = BonsaiLeaf leaf
  | BonsaiNode (UnionM (BonsaiTree leaf)) (UnionM (BonsaiTree leaf))
  deriving (Generic, Show, Eq, Hashable, NFData)

deriving via (Default (BonsaiTree leaf)) instance (SEq SymBool leaf) => SEq SymBool (BonsaiTree leaf)

deriving instance (Mergeable SymBool leaf) => Mergeable SymBool (BonsaiTree leaf)

deriving instance (Mergeable SymBool leaf, SymEval Model leaf) => SymEval Model (BonsaiTree leaf)

deriving instance (ToCon leaf cleaf) => ToCon (BonsaiTree leaf) (ConcBonsaiTree cleaf)

deriving instance
  (Mergeable SymBool leaf, ToSym cleaf leaf) =>
  ToSym (ConcBonsaiTree cleaf) (BonsaiTree leaf)

instance (Mergeable SymBool leaf, HasTrie leaf) => HasTrie (BonsaiTree leaf) where
  newtype BonsaiTree leaf :->: b = BonsaiTreeTrie {unBonsaiTreeTrie :: Reg (BonsaiTree leaf) :->: b}
  trie = trieGeneric BonsaiTreeTrie
  untrie = untrieGeneric unBonsaiTreeTrie
  enumerate = enumerateGeneric unBonsaiTreeTrie

$(makeUnionMWrapper "u" ''BonsaiTree)

showConcTree :: OptimSyntaxSpec n -> ConcBonsaiTree (UnsignedBV n) -> Maybe B.ByteString
showConcTree stx (ConcBonsaiLeaf sym) = bvToTerminal stx sym
showConcTree stx (ConcBonsaiNode l r) = do
  ls <- showConcTree stx l
  rs <- showConcTree stx r
  return $ B.append "[ " (B.append ls (B.append " " (B.append rs " ]")))

instance (KnownNat n, 1 <= n) => SymGen SymBool Int (BonsaiTree (SymUnsignedBV n)) where
  genSymIndexed depth =
    if depth <= 1
      then uBonsaiLeaf <$> genSymSimpleIndexed @SymBool ()
      else do
        l <- genSymIndexed $ depth - 1
        r <- genSymIndexed $ depth - 1
        sym <- genSymSimpleIndexed @SymBool ()
        choose (BonsaiLeaf sym) [BonsaiNode l r]

unsafeLeaf :: (KnownNat n, 1 <= n) => OptimSyntaxSpec n -> B.ByteString -> BonsaiTree (SymUnsignedBV n)
unsafeLeaf stx name = BonsaiLeaf $ conc $ fromJust $ terminalToBV stx name

data BonsaiError
  = BonsaiTypeError
  | BonsaiExecError
  | BonsaiRecursionError
  deriving (Show, Eq, Generic, Mergeable SymBool, ToCon BonsaiError, NFData, SymEval Model)

instance TransformError BonsaiError BonsaiError where
  transformError = id

data VerifyTyper a = VerifyTyper

instance SolverTranslation (VerifyTyper a) BonsaiError a where
  errorTranslation _ BonsaiExecError = True
  errorTranslation _ _ = False
  valueTranslation _ _ = conc False
