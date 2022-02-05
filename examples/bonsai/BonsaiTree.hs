{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module BonsaiTree where
import Grisette.Core
import Grisette.SymPrim.Term
import Data.BitVector.Sized.Unsigned
import GHC.Generics
import GHC.TypeNats
import Data.Hashable
import SyntaxSpec
import qualified Data.ByteString as B
import Data.Maybe
import Data.MemoTrie
import Control.DeepSeq

data ConcBonsaiTree n
  = ConcBonsaiLeaf (UnsignedBV n)
  | ConcBonsaiNode (ConcBonsaiTree n) (ConcBonsaiTree n)
  deriving (Show, Generic)

data BonsaiTree n
  = BonsaiLeaf (SymUnsignedBV n)
  | BonsaiNode (UnionM (BonsaiTree n)) (UnionM (BonsaiTree n))
  deriving Generic

deriving instance (KnownNat n, 1 <= n) => Show (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => Eq (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => SEq SymBool (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => Mergeable SymBool (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => ToCon (BonsaiTree n) (ConcBonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => ToSym (ConcBonsaiTree n) (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => SymEval Model (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => Hashable (BonsaiTree n)
deriving instance (KnownNat n, 1 <= n) => NFData (BonsaiTree n)

instance (KnownNat n, 1 <= n) => HasTrie (BonsaiTree n) where
  newtype (BonsaiTree n :->: b) = BonsaiTreeTrie { unBonsaiTreeTrie :: Reg (BonsaiTree n) :->: b}
  trie = trieGeneric BonsaiTreeTrie
  untrie = untrieGeneric unBonsaiTreeTrie
  enumerate = enumerateGeneric unBonsaiTreeTrie

$(makeUnionMWrapper "u" ''BonsaiTree)

showConcTree :: OptimSyntaxSpec n -> ConcBonsaiTree n -> Maybe B.ByteString
showConcTree stx (ConcBonsaiLeaf sym) = bvToTerminal stx sym
showConcTree stx (ConcBonsaiNode l r) = do
  ls <- showConcTree stx l
  rs <- showConcTree stx r
  return $ B.append "[ " (B.append ls (B.append " " (B.append rs " ]")))

instance (KnownNat n, 1 <= n) => SymGen SymBool Int (BonsaiTree n) where
  genSymIndexed depth = if depth <= 1 then
    uBonsaiLeaf <$> genSymSimpleIndexed @SymBool ()
    else do
      l <- genSymIndexed $ depth - 1
      r <- genSymIndexed $ depth - 1
      sym <- genSymSimpleIndexed @SymBool ()
      choose (BonsaiLeaf sym) [BonsaiNode l r]

unsafeLeaf :: (KnownNat n, 1 <= n) => OptimSyntaxSpec n -> B.ByteString -> BonsaiTree n
unsafeLeaf stx name = BonsaiLeaf $ conc $ fromJust $ terminalToBV stx name
