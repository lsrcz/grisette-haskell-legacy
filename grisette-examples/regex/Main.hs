{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Bifunctor
import qualified Data.ByteString.Char8 as B
import Data.Hashable
import Data.Maybe
import GHC.Generics
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Text.Regex.PCRE
import Utils.Timing
import qualified Data.ByteString.Char8 as C
import Grisette.Lib

type PattCoro = B.ByteString -> Coroutine (Yield (UnionM Integer)) UnionM ()

addYield :: Integer -> Coroutine (Yield (UnionM Integer)) UnionM () -> Coroutine (Yield (UnionM Integer)) UnionM ()
addYield n l = l |>>= \i -> mrgYield $ mrgReturn n + i

primPatt :: Char -> PattCoro
primPatt pattc = htmemo $ \str ->
  when (B.length str /= 0  && C.head str == pattc) $
    yield $ mrgReturn 1

seqPatt :: PattCoro -> PattCoro -> PattCoro
seqPatt patt1 patt2 = htmemo $ \str ->
  patt1 str |>>= (lift >=> (\i1 -> addYield i1 $ patt2 (B.drop (fromIntegral i1) str)))

altPatt :: PattCoro -> PattCoro -> PattCoro
altPatt patt1 patt2 = htmemo $ \str -> patt1 str >>~ patt2 str

emptyPatt :: PattCoro
emptyPatt = htmemo $ \_ -> yield 0

plusGreedyPatt :: PattCoro -> PattCoro
plusGreedyPatt patt = htmemo $ \str -> patt str |>>= (\i ->
    lift i >>= \i1 ->
      when (i1 /= 0) (addYield i1 $ plusGreedyPatt patt (B.drop (fromIntegral i1) str))
  >> yield i)

plusLazyPatt :: PattCoro -> PattCoro
plusLazyPatt patt = htmemo $ \str -> patt str |>>= \i -> yield i
  >> (lift i >>= \i1 -> when (i1 /= 0) (addYield i1 $ plusLazyPatt patt (B.drop (fromIntegral i1) str)))

plusPatt :: SymBool -> PattCoro -> PattCoro
plusPatt greedy = mrgIte greedy plusGreedyPatt plusLazyPatt

matchFirstWithStartImpl :: PattCoro -> B.ByteString -> Integer -> MaybeT UnionM Integer
matchFirstWithStartImpl patt str startPos = case merge $ pogoStick (\(Yield idx _) -> return $ mrgLift idx) r1 of
  SingleU x -> x
  _ -> error "Should not happen"
  where
    r1 = (\_ -> MaybeT $ return Nothing)
      <$> addYield startPos (patt (B.drop (fromIntegral startPos) str))

matchFirstImpl :: PattCoro -> B.ByteString -> MaybeT UnionM (Integer, Integer)
matchFirstImpl patt str =
  mrgMsum $ (\s -> (\t -> (s, t - s)) <$> matchFirstWithStartImpl patt str s) <$> [0 .. toInteger $ B.length str]

data ConcPatt
  = ConcPrimPatt Char
  | ConcSeqPatt ConcPatt ConcPatt
  | ConcAltPatt ConcPatt ConcPatt
  | ConcPlusPatt ConcPatt Bool
  | ConcEmptyPatt
  deriving (Show, Generic, ToCon Patt)

data Patt
  = PrimPatt Char
  | SeqPatt (UnionM Patt) (UnionM Patt)
  | AltPatt (UnionM Patt) (UnionM Patt)
  | PlusPatt (UnionM Patt) SymBool
  | EmptyPatt
  deriving (Show, Generic, Eq, Hashable, ToSym ConcPatt, SymEval Model, Mergeable SymBool)

toCoroU :: UnionM Patt -> PattCoro
toCoroU u = getSingle $ mrgFmap toCoro u

toCoro :: Patt -> PattCoro
toCoro = htmemo $ \case
  PrimPatt s -> primPatt s
  SeqPatt p1 p2 -> seqPatt (toCoroU p1) (toCoroU p2)
  AltPatt p1 p2 -> altPatt (toCoroU p1) (toCoroU p2)
  PlusPatt subp greedy -> plusPatt greedy (toCoroU subp)
  EmptyPatt -> emptyPatt

conformsFirst :: PattCoro -> B.ByteString -> B.ByteString -> SymBool
conformsFirst patt reg str =
  let rp = matchFirstImpl patt str
      rc = bimap toInteger toInteger <$> listToMaybe (getAllMatches (str =~ reg) :: [(Int, Int)])
      rc1 = MaybeT $ mrgReturn rc
   in rp ==~ rc1

synthesisRegexCompiled :: GrisetteSMTConfig b -> UnionM Patt -> PattCoro -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegexCompiled config patt coro reg strs =
  let constraints = (\x -> (conformsFirst coro reg x)) <$> strs
      constraint = foldr (&&~) (conc True) constraints
   in do
        _ <- timeItAll "symeval" $ constraint `deepseq` return ()
        solveRes <- timeItAll "lowering/solving" $ solveWith config constraint
        case solveRes of
          Left _ -> return Nothing
          Right mo -> return $ Just $ symevalToCon mo patt

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

test8 :: PattCoro
test8 = toCoro $ toSym $ ConcSeqPatt (ConcAltPatt (ConcPrimPatt 'c') (ConcPrimPatt 'd'))
  (ConcPlusPatt (ConcSeqPatt (ConcAltPatt (ConcPrimPatt 'a') ConcEmptyPatt) (ConcPrimPatt 'b')) False)

reg8 :: B.ByteString
reg8 = "(c|d)(a?b)+?"

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
  runSymGenIndexed
    (choose (PrimPatt 'a') [PrimPatt 'b'])
    "a"
-}

freshPrim :: State (Int, String) (UnionM Patt)
freshPrim = choose (PrimPatt 'd') [PrimPatt 'c', PrimPatt 'b', PrimPatt 'a', EmptyPatt]

binFreshPrim :: (UnionM Patt -> UnionM Patt -> Patt) -> State (Int, String) Patt
binFreshPrim f = do
  f1 <- freshPrim
  f f1 <$> freshPrim

seqOrAlt :: State (Int, String) (UnionM Patt)
seqOrAlt = do
  s <- binFreshPrim SeqPatt
  a <- binFreshPrim AltPatt
  choose s [a]

sks :: State (Int, String) Patt
sks = do
  s1 <- seqOrAlt
  s2 <- seqOrAlt
  f1 <- freshPrim
  b <- genSymSimpleIndexed @SymBool ()
  let s3 = SeqPatt s1 f1
  let p = PlusPatt (mrgReturn s3) b
  return $ SeqPatt s2 (mrgReturn p)

sk :: Patt
sk = runSymGenIndexed sks "a"

r :: Patt
r =
  toSym $
    ConcSeqPatt
      (ConcAltPatt (ConcPrimPatt 'c') (ConcPrimPatt 'd'))
      (ConcPlusPatt (ConcSeqPatt (ConcAltPatt ConcEmptyPatt (ConcPrimPatt 'a')) (ConcPrimPatt 'b')) True)

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
main = do
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
  print $ matchFirstImpl test8 "cabab"
  print $ listToMaybe (getAllMatches (("cabab" :: B.ByteString) =~ reg8) :: [(Int, Int)])
  print sk1
  -}
  res <- synthesisRegex (UnboundedReasoning z3 {transcript = Just "/tmp/a.smt2", timing = PrintTiming}) (mrgReturn sk) "[cd](a?b)+?" $ genWordsUpTo 5 "abcd"
  print res
  case res of
    Just resv -> do
      print $ matchFirstImpl (toCoro $ toSym resv) "cabab"
      print $ listToMaybe (getAllMatches (("cabab" :: B.ByteString) =~ ("[cd](a?b)+?" :: B.ByteString)) :: [(Int, Int)])
    Nothing -> putStrLn "Failed"
