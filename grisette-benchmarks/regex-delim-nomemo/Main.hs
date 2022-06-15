{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.DeepSeq
import Control.Monad.Cont
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Hashable
import Data.Maybe
import GHC.Generics
import Grisette
import Text.Regex.PCRE
import Utils.Timing

data Thread m a = Done | Resume a (m (Thread m a))

yield :: (Monad m) => a -> ContT (Thread m a) m ()
yield x = shiftT (\k -> return $ Resume x (k ()))

instance (Mergeable1 bool m, Mergeable bool a) => Mergeable bool (Thread m a) where
  mergeStrategy = mergeStrategy1

instance Mergeable1 bool m => Mergeable1 bool (Thread m) where
  liftMergeStrategy ms =
    OrderedStrategy
      (\case Done -> False; Resume {} -> True)
      ( \case
          False -> SimpleStrategy $ \_ t _ -> t
          True -> wrapMergeStrategy2 Resume (\(Resume l r) -> (l, r)) ms (liftMergeStrategy (liftMergeStrategy ms))
      )

type CoroBase a = ContT (Thread UnionM (UnionM Int)) UnionM a

type Coro = CoroBase (Thread UnionM (UnionM Int))

type PattCoro = B.ByteString -> Int -> Coro

pipe :: Coro -> (UnionM Int -> CoroBase a) -> Coro
pipe c f = do
  let l = mrgEvalContT c
  lift l >>= check
  where
    check Done = return Done
    check (Resume x m) = f x >> (lift m >>= check)

unlim :: Coro -> Coro
unlim c = pipe c yield

primPatt :: Char -> PattCoro
primPatt pattc = htmemo2 $ \str idx ->
  mrgResetT $
    if B.length str > idx && C.index str idx == pattc
      then yield (mrgReturn $ idx + 1) >> return Done
      else return Done

seqPatt :: PattCoro -> PattCoro -> PattCoro
seqPatt patt1 patt2 = htmemo2 $ \str idx -> mrgResetT $ pipe (patt1 str idx) (lift >=> unlim . patt2 str)

altPatt :: PattCoro -> PattCoro -> PattCoro
altPatt patt1 patt2 = htmemo2 $ \str idx -> mrgResetT $ unlim (patt1 str idx) >> unlim (patt2 str idx)

emptyPatt :: PattCoro
emptyPatt = htmemo2 $ \str idx ->
  mrgResetT $ when (B.length str >= idx) (yield $ mrgReturn idx) >> return Done

plusGreedyPatt :: PattCoro -> PattCoro
plusGreedyPatt patt = htmemo2 $ \str idx ->
  mrgResetT $
    pipe
      (patt str idx)
      ( \i -> do
          i1 <- lift i
          if i1 /= idx then unlim (plusGreedyPatt patt str i1) >> yield (mrgReturn i1) else yield (mrgReturn i1) -- ?
      )

plusLazyPatt :: PattCoro -> PattCoro
plusLazyPatt patt = htmemo2 $ \str idx ->
  mrgResetT $
    pipe
      (patt str idx)
      ( \i -> do
          i1 <- lift i
          if i1 /= idx then yield (mrgReturn i1) >> unlim (plusLazyPatt patt str i1) else yield (mrgReturn i1) >> return Done -- ?
      )

plusPatt :: SymBool -> PattCoro -> PattCoro
plusPatt greedy patt = htmemo2 $ \str idx ->
  mrgResetT $ mrgIte greedy (plusGreedyPatt patt str idx) (plusLazyPatt patt str idx)

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

-- Compiling a Patt to pattern coroutine
toCoroU :: UnionM Patt -> PattCoro
toCoroU u = getSingle $ mrgFmap toCoro u

toCoro :: Patt -> PattCoro
toCoro = htmemo $ \case
  PrimPatt s -> primPatt s
  SeqPatt p1 p2 -> seqPatt (toCoroU p1) (toCoroU p2)
  AltPatt p1 p2 -> altPatt (toCoroU p1) (toCoroU p2)
  PlusPatt subp greedy -> plusPatt greedy (toCoroU subp)
  EmptyPatt -> emptyPatt

matchFirstWithStartImpl :: PattCoro -> B.ByteString -> Int -> MaybeT UnionM Int
matchFirstWithStartImpl patt str startPos = MaybeT $ x >>= f
  where
    x = mrgEvalContT (patt str startPos)
    f Done = mrgReturn Nothing
    f (Resume a _) = mrgFmap Just a

matchFirstImpl :: PattCoro -> B.ByteString -> MaybeT UnionM (Int, Int)
matchFirstImpl patt str =
  mrgMsum $ (\s -> (\t -> (s, t - s)) <$> matchFirstWithStartImpl patt str s) <$> [0 .. B.length str]

-- Check if the first match returned by the coroutine matcher is the same as the first match returned by 'regex-pcre' package.
conformsFirst :: PattCoro -> B.ByteString -> B.ByteString -> SymBool
conformsFirst patt reg str =
  let rp = matchFirstImpl patt str
      rc = listToMaybe (getAllMatches (str =~ reg) :: [(Int, Int)])
      rc1 = MaybeT $ mrgReturn rc
   in rp ==~ rc1

-- Synthesis a regex such that has the same semantics with a concrete regex on a set of strings.
synthesisRegexCompiled :: GrisetteSMTConfig b -> UnionM Patt -> PattCoro -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegexCompiled config patt coro reg strs =
  let constraints = conformsFirst coro reg <$> strs
      constraint = foldr (&&~) (conc True) constraints
   in do
        _ <- timeItAll "evaluate" $ constraint `deepseq` return ()
        solveRes <- timeItAll "Lowering/Solving" $ solveFormula config constraint
        case solveRes of
          Left _ -> return Nothing
          Right mo -> return $ Just $ evaluateToCon mo patt

synthesisRegex :: GrisetteSMTConfig b -> UnionM Patt -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegex config patt = synthesisRegexCompiled config patt (toCoroU patt)

test1 :: PattCoro
test1 = toCoro $ toSym $ ConcPrimPatt 'a'

reg1 :: B.ByteString
reg1 = "a"

test2 :: PattCoro
test2 = toCoro $ toSym $ ConcSeqPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')

reg2 :: B.ByteString
reg2 = "ab"

test3 :: PattCoro
test3 = toCoro $ toSym $ ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')

reg3 :: B.ByteString
reg3 = "a|b"

test4 :: PattCoro
test4 = toCoro $ toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')) True

reg4 :: B.ByteString
reg4 = "(a|b)+"

test5 :: PattCoro
test5 = toCoro $ toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')) False

reg5 :: B.ByteString
reg5 = "(a|b)+?"

test6 :: PattCoro
test6 = toCoro $ toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt (ConcPrimPatt 'a') (ConcPrimPatt 'b')) False) (ConcPrimPatt 'c')

test7 :: PattCoro
test7 = toCoro $ toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) False) (ConcPrimPatt 'c')

reg6 :: B.ByteString
reg6 = "((a|b)+?)c"

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

sk1 :: UnionM Patt
sk1 =
  runGenSymFresh
    (choose [PrimPatt 'a', PrimPatt 'b'])
    "a"

-- Creating regex sketch using 'GenSymFresh' monad. (The monad used by 'SymGen' class in the paper, or 'GenSym' class in the current Grisette version)
freshPrim :: GenSymFresh (UnionM Patt)
freshPrim = choose [PrimPatt 'd', PrimPatt 'c', PrimPatt 'b', PrimPatt 'a', EmptyPatt]

binFreshPrim :: (UnionM Patt -> UnionM Patt -> Patt) -> GenSymFresh Patt
binFreshPrim f = do
  f1 <- freshPrim
  f f1 <$> freshPrim

seqOrAlt :: GenSymFresh (UnionM Patt)
seqOrAlt = do
  s <- binFreshPrim SeqPatt
  a <- binFreshPrim AltPatt
  choose [s, a]

sks :: GenSymFresh Patt
sks = do
  s1 <- seqOrAlt
  s2 <- seqOrAlt
  f1 <- freshPrim
  b <- genSymSimpleFresh @SymBool ()
  let s3 = SeqPatt s1 f1
  let p = PlusPatt (mrgReturn s3) b
  return $ SeqPatt s2 (mrgReturn p)

sk :: Patt
sk = runGenSymFresh sks "a"

ref :: Patt
ref =
  toSym $
    ConcSeqPatt
      (ConcAltPatt (ConcPrimPatt 'c') (ConcPrimPatt 'd'))
      (ConcPlusPatt (ConcSeqPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) (ConcPrimPatt 'b')) True)

{-
t :: [Word8]
t = ['a', 'b', 'c', 'd']
-}

-- Generating a set of strings.
genWords :: Int -> [Char] -> [B.ByteString]
genWords 0 _ = [B.empty]
genWords n alph = [C.cons ch w | w <- genWords (n - 1) alph, ch <- alph]

genWordsUpTo :: Int -> [Char] -> [B.ByteString]
genWordsUpTo n alph = concatMap (`genWords` alph) [0 .. n]

main :: IO ()
main = timeItAll "Overall" $ do
  {-
  print $ matchFirstImpl test1 str1
  print $ listToMaybe (getAllMatches (str1 =~ reg1) :: [(Int, Int)])
  print $ matchFirstImpl test2 str1
  print $ listToMaybe (getAllMatches (str1 =~ reg2) :: [(Int, Int)])
  print $ matchFirstImpl test2 str2
  print $ listToMaybe (getAllMatches (str2 =~ reg2) :: [(Int, Int)])
  print $ matchFirstImpl test2 str3
  print $ listToMaybe (getAllMatches (str3 =~ reg2) :: [(Int, Int)])
  print $ matchFirstImpl test2 str4
  print $ listToMaybe (getAllMatches (str4 =~ reg2) :: [(Int, Int)])
  print $ matchFirstImpl test3 str5
  print $ listToMaybe (getAllMatches (str5 =~ reg3) :: [(Int, Int)])
  print $ matchFirstImpl test3 str2
  print $ listToMaybe (getAllMatches (str2 =~ reg3) :: [(Int, Int)])
  print $ matchFirstImpl test3 str3
  print $ listToMaybe (getAllMatches (str3 =~ reg3) :: [(Int, Int)])
  print $ matchFirstImpl test3 str6
  print $ listToMaybe (getAllMatches (str6 =~ reg3) :: [(Int, Int)])
  print $ matchFirstImpl test4 str3
  print $ listToMaybe (getAllMatches (str3 =~ reg4) :: [(Int, Int)])
  print $ matchFirstImpl test5 str3
  print $ listToMaybe (getAllMatches (str3 =~ reg5) :: [(Int, Int)])
  print $ matchFirstImpl test6 str7
  print $ listToMaybe (getAllMatches (str7 =~ reg6) :: [(Int, Int)])
  print sk1
  -}

  res <- synthesisRegex (UnboundedReasoning z3 {transcript = Just "/tmp/a.smt2", timing = PrintTiming}) (mrgReturn sk) "[cd](a?b)+?" $ genWordsUpTo 5 "abcd"
  print res
  -- The synthesized regex
  -- Just (ConcSeqPatt (ConcAltPatt (ConcPrimPatt 'c') (ConcPrimPatt 'd')) (ConcPlusPatt (ConcSeqPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) (ConcPrimPatt 'b')) False))
  print $ matchFirstImpl (toCoro ref) "cabab"
  print $ listToMaybe (getAllMatches (("cabab" :: B.ByteString) =~ ("[cd](a?b)+?" :: B.ByteString)) :: [(Int, Int)])