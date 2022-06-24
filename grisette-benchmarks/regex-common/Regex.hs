{-# LANGUAGE OverloadedStrings #-}

module Regex where
import GHC.Generics
import Grisette
import Data.Hashable
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C

-- The regex patterns. In the paper it is call Regex.
-- PrimPatt 'a'        --> a
-- SeqPatt patt1 patt2 --> (patt1)(patt2)
-- AltPatt patt1 patt2 --> (patt1) | (patt2)
-- PlusPatt patt False --> (patt)+?         lazy match
-- PlusPatt patt True  --> (patt)+         greedy match
-- EmptyPatt           --> epsilon
data ConcPatt
  = ConcPrimPatt Char
  | ConcSeqPatt ConcPatt ConcPatt
  | ConcAltPatt ConcPatt ConcPatt
  | ConcPlusPatt ConcPatt Bool
  | ConcEmptyPatt
  deriving (Show, Generic)
  deriving (ToCon Patt) via (Default ConcPatt)

-- In the paper it is called SRegex
data Patt
  = PrimPatt Char
  | SeqPatt (UnionM Patt) (UnionM Patt)
  | AltPatt (UnionM Patt) (UnionM Patt)
  | PlusPatt (UnionM Patt) SymBool
  | EmptyPatt
  deriving (Show, Generic, Eq, Hashable)
  deriving (ToSym ConcPatt, Evaluate Model, Mergeable SymBool) via (Default Patt)

-- Creating regex sketch using 'GenSymFresh' monad. (The monad used by 'SymGen' class in the paper, or 'GenSym' class in the current Grisette version)
freshPrim :: GenSymFresh (UnionM Patt)
freshPrim = choose [PrimPatt 'd', PrimPatt 'c', PrimPatt 'b', PrimPatt 'a', EmptyPatt]

binFreshPrim :: (UnionM Patt -> UnionM Patt -> GenSymFresh (UnionM Patt)) -> GenSymFresh (UnionM Patt)
binFreshPrim f = do
  f1 <- freshPrim
  f2 <- freshPrim
  f f1 f2

seqOrAlt :: GenSymFresh (UnionM Patt)
seqOrAlt = binFreshPrim (\l r -> choose [SeqPatt l r, AltPatt l r])

sketchGen :: GenSymFresh Patt
sketchGen = do
  s1 <- seqOrAlt
  f1 <- freshPrim
  s2 <- choose [SeqPatt s1 f1, AltPatt s1 f1]
  greedy <- genSymSimpleFresh @SymBool ()
  let p = PlusPatt s2 greedy
  s3 <- seqOrAlt
  return $ SeqPatt s3 (mrgReturn p)

sketch :: Patt
sketch = runGenSymFresh sketchGen "a"

ref :: Patt
ref =
  toSym $
    ConcSeqPatt
      (ConcAltPatt (ConcPrimPatt 'c') (ConcPrimPatt 'd'))
      (ConcPlusPatt (ConcSeqPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) (ConcPrimPatt 'b')) False)

-- Generating a set of strings.
genWords :: Int -> [Char] -> [B.ByteString]
genWords 0 _ = [B.empty]
genWords n alph = [C.cons ch w | w <- genWords (n - 1) alph, ch <- alph]

genWordsUpTo :: Int -> [Char] -> [B.ByteString]
genWordsUpTo n alph = concatMap (`genWords` alph) [0 .. n]

