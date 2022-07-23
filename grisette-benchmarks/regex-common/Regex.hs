{-# LANGUAGE OverloadedStrings #-}

module Regex where
import GHC.Generics
import Grisette
import Data.Hashable
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.DeepSeq
import Utils.Timing
import Data.Maybe
import Text.Regex.PCRE

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
binFreshPrim f = freshPrim >>= \p1 -> freshPrim >>= \p2 -> f p1 p2

seqOrAlt :: GenSymFresh (UnionM Patt)
seqOrAlt = binFreshPrim (\l r -> choose [SeqPatt l r, AltPatt l r])

sketchGen :: GenSymFresh Patt
sketchGen = do
  s1 <- seqOrAlt
  f1 <- freshPrim
  s2 <- choose [SeqPatt s1 f1, AltPatt s1 f1]
  greedy <- genSymSimpleFresh ()
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

class RegexSynth tag where
  type PattCoroType tag
  toCoro :: proxy tag -> Patt -> PattCoroType tag
  matchFirstWithStart :: proxy tag -> PattCoroType tag -> B.ByteString -> Int -> MaybeT UnionM Int

toCoroU :: (RegexSynth tag, SimpleMergeable (Sym Bool) (PattCoroType tag)) =>
  proxy tag -> UnionM Patt -> PattCoroType tag
toCoroU tag u = getSingle $ mrgFmap (toCoro tag) u
{-# INLINE toCoroU #-}

matchFirst :: RegexSynth tag => proxy tag -> PattCoroType tag -> B.ByteString -> MaybeT UnionM (Int, Int)
matchFirst tag patt str =
  mrgMsum $ (\s -> (\t -> (s, t - s)) <$> matchFirstWithStart tag patt str s) <$> [0 .. B.length str]
{-# INLINE matchFirst #-}

conformsFirst :: RegexSynth tag => proxy tag -> PattCoroType tag -> B.ByteString -> B.ByteString -> SymBool
conformsFirst tag patt reg str =
  let rp = matchFirst tag patt str
      rc = listToMaybe (getAllMatches (str =~ reg) :: [(Int, Int)])
      rc1 = MaybeT $ mrgReturn rc
   in rp ==~ rc1
{-# INLINE conformsFirst #-}

-- Synthesis a regex such that has the same semantics with a concrete regex on a set of strings.
synthesisRegexCompiled :: RegexSynth tag => proxy tag -> GrisetteSMTConfig b -> UnionM Patt -> PattCoroType tag -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegexCompiled tag config patt coro reg strs =
  let constraints = conformsFirst tag coro reg <$> strs
      constraint = foldr (&&~) (conc True) constraints
   in do
        _ <- timeItAll "evaluate" $ constraint `deepseq` return ()
        solveRes <- timeItAll "Lowering/Solving" $ solveFormula config constraint
        case solveRes of
          Left _ -> return Nothing
          Right mo -> return $ Just $ evaluateToCon mo patt
{-# INLINE synthesisRegexCompiled #-}

synthesisRegex :: (RegexSynth tag, SimpleMergeable (Sym Bool) (PattCoroType tag)) =>
  proxy tag -> GrisetteSMTConfig b -> UnionM Patt -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegex tag config patt = synthesisRegexCompiled tag config patt (toCoroU tag patt)
{-# INLINE synthesisRegex #-}

test1 :: Patt
test1 = toSym $ ConcPrimPatt 'a'

reg1 :: B.ByteString
reg1 = "a"

test2 :: Patt
test2 = toSym $ ConcSeqPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')

reg2 :: B.ByteString
reg2 = "ab"

test3 :: Patt
test3 = toSym $ ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')

reg3 :: B.ByteString
reg3 = "a|b"

test4 :: Patt
test4 = toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')) True

reg4 :: B.ByteString
reg4 = "(a|b)+"

test5 :: Patt
test5 = toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')) False

reg5 :: B.ByteString
reg5 = "(a|b)+?"

test6 :: Patt
test6 = toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')) False) (ConcPrimPatt 'c')

reg6 :: B.ByteString
reg6 = "((a|b)+?)c"

test7 :: Patt
test7 = toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) False) (ConcPrimPatt 'c')

reg7 :: B.ByteString
reg7 = "((a?)+?)c"

str1 :: B.ByteString
str1 = "babba"

str2 :: B.ByteString
str2 = "cbaaba"

str3 :: B.ByteString
str3 = "caaba"

str4 :: B.ByteString
str4 = "cbaaa"

str5 :: B.ByteString
str5 = "baaba"

str6 :: B.ByteString
str6 = "c"

str7 :: B.ByteString
str7 = "c"

testPatt :: RegexSynth tag => proxy tag -> B.ByteString -> B.ByteString -> Patt -> IO ()
testPatt tag str refreg patt = do
  let resRef = listToMaybe (getAllMatches (str =~ refreg) :: [(Int, Int)])
  let resPatt = case runMaybeT $ matchFirst tag (toCoro tag patt) str of SingleU v -> v; _ -> undefined
  when (resRef /= resPatt) $ fail $ unlines ["Failed on ", show str, show refreg, show patt]
{-# INLINE testPatt #-}

test :: RegexSynth tag => proxy tag -> IO ()
test tag = do
  testPatt tag str1 reg1 test1
  testPatt tag str1 reg2 test2
  testPatt tag str2 reg2 test2
  testPatt tag str3 reg2 test2
  testPatt tag str4 reg2 test2
  testPatt tag str5 reg3 test3
  testPatt tag str2 reg3 test3
  testPatt tag str3 reg3 test3
  testPatt tag str6 reg3 test3
  testPatt tag str3 reg4 test4
  testPatt tag str3 reg5 test5
  testPatt tag str7 reg6 test6
{-# INLINE test #-}

regexMain :: (RegexSynth tag, SimpleMergeable (Sym Bool) (PattCoroType tag)) => proxy tag -> IO ()
regexMain tag = do
  let config = UnboundedReasoning z3 {timing = PrintTiming}
  test tag

  res <- synthesisRegex tag config (mrgReturn sketch) "[cd](a?b)*?(a?b)" $ genWordsUpTo 5 "abcd"
  print res
  -- The synthesized regex
  -- Just (ConcSeqPatt (ConcAltPatt (ConcPrimPatt 'c') (ConcPrimPatt 'd')) (ConcPlusPatt (ConcSeqPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) (ConcPrimPatt 'b')) False))
  print $ matchFirst tag (toCoro tag ref) "cabab"
  print $ listToMaybe (getAllMatches (("cabab" :: B.ByteString) =~ ("[cd](a?b)+?" :: B.ByteString)) :: [(Int, Int)])
{-# INLINE regexMain #-}
