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
import Data.Proxy
import Generics.Deriving
import GHC.TypeNats
import Grisette
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

deriving via (Default (BonsaiTree leaf)) instance (Mergeable SymBool leaf) => Mergeable SymBool (BonsaiTree leaf)

deriving via (Default (BonsaiTree leaf)) instance (Mergeable SymBool leaf, Evaluate Model leaf) => Evaluate Model (BonsaiTree leaf)

deriving via (Default (ConcBonsaiTree cleaf)) instance (ToCon leaf cleaf) => ToCon (BonsaiTree leaf) (ConcBonsaiTree cleaf)

deriving via (Default (BonsaiTree leaf)) instance
  (Mergeable SymBool leaf, ToSym cleaf leaf) =>
  ToSym (ConcBonsaiTree cleaf) (BonsaiTree leaf)

$(makeUnionMWrapper "u" ''BonsaiTree)

showConcTree :: OptimSyntaxSpec n -> ConcBonsaiTree (UnsignedBV n) -> Maybe B.ByteString
showConcTree stx (ConcBonsaiLeaf sym) = bvToTerminal stx sym
showConcTree stx (ConcBonsaiNode l r) = do
  ls <- showConcTree stx l
  rs <- showConcTree stx r
  return $ B.append "[ " (B.append ls (B.append " " (B.append rs " ]")))

instance (KnownNat n, 1 <= n) => GenSym SymBool Int (BonsaiTree (SymUnsignedBV n)) where
  genSymFresh depth =
    if depth <= 1
      then uBonsaiLeaf <$> genSymSimpleFresh (Proxy :: Proxy SymBool) ()
      else do
        l <- genSymFresh $ depth - 1
        r <- genSymFresh $ depth - 1
        sym <- genSymSimpleFresh (Proxy :: Proxy SymBool) ()
        choose [BonsaiLeaf sym, BonsaiNode l r]

unsafeLeaf :: (KnownNat n, 1 <= n) => OptimSyntaxSpec n -> B.ByteString -> BonsaiTree (SymUnsignedBV n)
unsafeLeaf stx nm = BonsaiLeaf $ conc $ fromJust $ terminalToBV stx nm

data BonsaiError
  = BonsaiTypeError
  | BonsaiExecError
  | BonsaiRecursionError
  deriving (Show, Eq, Generic, NFData)
  deriving (Mergeable SymBool, ToCon BonsaiError, Evaluate Model) via (Default BonsaiError)

instance TransformError BonsaiError BonsaiError where
  transformError = id

data VerifyTyper = VerifyTyper

instance SolverErrorTranslation VerifyTyper BonsaiError where
  errorTranslation _ BonsaiExecError = True
  errorTranslation _ _ = False

instance SolverTranslation VerifyTyper SymBool BonsaiError a where
  valueTranslation _ _ = conc False
