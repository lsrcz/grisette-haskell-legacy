{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Char8 as C
import Data.Hashable
import Data.Maybe
import GHC.Generics
import Grisette
import Text.Regex.PCRE
import Transducer
import Utils.Timing

type PattCoro = B.ByteString -> Int -> Coroutine (Yield (UnionM Int)) UnionM ()

primPatt :: Char -> PattCoro
primPatt pattc str idx =
  when (B.length str > idx && C.index str idx == pattc) $
    yield $ mrgReturn $ idx + 1

seqPatt :: PattCoro -> PattCoro -> PattCoro
seqPatt patt1 patt2 str idx =
  patt1 str idx |>>= (lift >=> patt2 str)

altPatt :: PattCoro -> PattCoro -> PattCoro
altPatt patt1 patt2 str idx = patt1 str idx >> patt2 str idx

emptyPatt :: PattCoro
emptyPatt str idx = when (B.length str >= idx) $ yield $ mrgReturn idx

plusPatt :: PattCoro -> SymBool -> PattCoro
plusPatt patt greedy str idx =
  patt str idx
    |>>= ( lift >=> \i1 ->
             mrgIf
               greedy
               (when (i1 /= idx) (plusPatt patt (conc True) str i1) >> yield (mrgReturn i1))
               (yield (mrgReturn i1) >> when (i1 /= idx) (plusPatt patt (conc False) str i1))
         )

matchFirstWithStartImpl :: PattCoro -> B.ByteString -> Int -> MaybeT UnionM Int
matchFirstWithStartImpl patt str startPos = case merge $ pogoStick (\(Yield idx _) -> return $ mrgLift idx) r1 of
  SingleU x -> x
  _ -> error "Should not happen"
  where
    r1 = (\_ -> MaybeT $ return Nothing) <$> patt str startPos

matchFirstImpl :: PattCoro -> B.ByteString -> MaybeT UnionM (Int, Int)
matchFirstImpl patt str =
  mrgMsum $ (\s -> (\t -> (s, t - s)) <$> matchFirstWithStartImpl patt str s) <$> [0 .. B.length str]

data ConcPatt
  = ConcPrimPatt Char
  | ConcSeqPatt ConcPatt ConcPatt
  | ConcAltPatt ConcPatt ConcPatt
  | ConcPlusPatt ConcPatt Bool
  | ConcEmptyPatt
  deriving (Show, Generic)
  deriving (ToCon Patt) via (Default ConcPatt)

data Patt
  = PrimPatt Char
  | SeqPatt (UnionM Patt) (UnionM Patt)
  | AltPatt (UnionM Patt) (UnionM Patt)
  | PlusPatt (UnionM Patt) SymBool
  | EmptyPatt
  deriving (Show, Generic, Eq, Hashable)
  deriving (ToSym ConcPatt, Evaluate Model, Mergeable SymBool) via (Default Patt)

toCoroU :: UnionM Patt -> PattCoro
toCoroU u = getSingle $ mrgFmap toCoro u

toCoro :: Patt -> PattCoro
toCoro = \case
  PrimPatt s -> primPatt s
  SeqPatt p1 p2 -> seqPatt (toCoroU p1) (toCoroU p2)
  AltPatt p1 p2 -> altPatt (toCoroU p1) (toCoroU p2)
  PlusPatt subp greedy -> plusPatt (toCoroU subp) greedy
  EmptyPatt -> emptyPatt

conformsFirst :: PattCoro -> B.ByteString -> B.ByteString -> SymBool
conformsFirst patt reg str =
  let rp = matchFirstImpl patt str
      rc = listToMaybe (getAllMatches (str =~ reg) :: [(Int, Int)])
      rc1 = MaybeT $ mrgReturn rc
   in rp ==~ rc1

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

{-
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
    (choose (PrimPatt 'a') [PrimPatt 'b'])
    "a"
    -}

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

{-
t :: [Word8]
t = ['a', 'b', 'c', 'd']
-}

genWords :: Int -> [Char] -> [B.ByteString]
genWords 0 _ = [B.empty]
genWords n alph = [B.cons ch w | w <- genWords (n - 1) alph, ch <- alph]

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
  res <- synthesisRegex (UnboundedReasoning z3 {timing = PrintTiming}) (mrgReturn sketch) "[cd](a?b)+?" $ genWordsUpTo 5 "abcd"
  print res
  print $ matchFirstImpl (toCoro ref) "cabab"
  print $ listToMaybe (getAllMatches (("cabab" :: B.ByteString) =~ ("[cd](a?b)+?" :: B.ByteString)) :: [(Int, Int)])
