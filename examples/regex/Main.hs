{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Memo as MM
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Bifunctor
import qualified Data.ByteString.Char8 as B
import Data.Functor.Sum
import Data.Hashable
import Data.Maybe
import Data.MemoTrie
import GHC.Generics
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import System.CPUTime
import Text.Printf
import Text.Regex.PCRE

time :: IO t -> IO t
time a = do
  start <- getCPUTime
  v <- a
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10 ^ (12 :: Integer))
  printf "Computation time: %0.3f sec\n" (diff :: Double)
  return v

bs :: Either () (Char, B.ByteString) -> B.ByteString
bs = either (const B.empty) (uncurry B.cons)

debs :: B.ByteString -> Either () (Char, B.ByteString)
debs b = case B.uncons b of
  Just p -> Right p
  Nothing -> Left ()

mrgSuspend ::
  forall m s bool x.
  (Monad m, Functor s, UnionMOp bool m, SymBoolOp bool, Mergeable bool x, Mergeable1 bool s) =>
  s (Coroutine s m x) ->
  Coroutine s m x
mrgSuspend s = withMergeable @bool @s @(Coroutine s m x) $ Coroutine $ mrgReturn @bool (Left s)

mrgYield :: (Monad m, SymBoolOp bool, UnionMOp bool m, Mergeable bool x) => x -> Coroutine (Yield x) m ()
mrgYield x = mrgSuspend (Yield x $ mrgReturn ())

mrgMapSuspension ::
  forall s m bool x s'.
  (Functor s, Monad m, SymBoolOp bool, UnionMOp bool m, Mergeable bool x, Mergeable1 bool s') =>
  (forall y. s y -> s' y) ->
  Coroutine s m x ->
  Coroutine s' m x
mrgMapSuspension f cort = withMergeable @bool @s' @(Coroutine s' m x) Coroutine {resume = mrgFmap map' $ resume cort}
  where
    map' :: Either (s (Coroutine s m x)) x -> Either (s' (Coroutine s' m x)) x
    map' (Right r1) = Right r1
    map' (Left s) = Left $ f $ mrgMapSuspension f <$> s

simpleTransducer ::
  (Monad m, SymBoolOp bool, UnionMOp bool m, Mergeable bool a, Mergeable bool x) =>
  (a -> Coroutine (Yield x) m ()) ->
  Coroutine (Sum (Await a) (Yield x)) m ()
simpleTransducer f = mrgSuspend (InL $ Await $ \x -> mapSuspension InR (f x) >> simpleTransducer f)

weaveYieldTransducer ::
  (Monad m, SymBoolOp bool, UnionMOp bool m, Mergeable bool b) =>
  WeaveStepper (Yield a) (Sum (Await a) (Yield b)) (Yield b) m () () ()
weaveYieldTransducer _ _ (Right ()) = mrgReturn ()
weaveYieldTransducer w (Left l) (Left (InR (Yield y c1))) = mrgSuspend (Yield y $ w (suspend l) c1)
weaveYieldTransducer w (Left (Yield x c)) (Left (InL (Await f))) = w c $ f x
weaveYieldTransducer _ (Right ()) (Left (InL (Await _))) = mrgReturn ()
weaveYieldTransducer w (Right ()) (Left (InR (Yield y c1))) = mrgSuspend (Yield y $ w (return ()) c1)

type PattCoro = B.ByteString -> Integer -> Coroutine (Yield (UnionM Integer)) UnionM ()

primPatt :: B.ByteString -> PattCoro
primPatt pattstr = memo2 $ \str idx -> -- trace (show pattstr ++ " " ++ show str ++ " " ++ show idx)
  when (idx + toInteger (B.length pattstr) <= toInteger (B.length str) && pattstr == B.take (B.length pattstr) (B.drop (fromInteger idx) str)) $
    yield $ mrgReturn $ idx + toInteger (B.length pattstr)

seqPatt :: PattCoro -> PattCoro -> PattCoro
seqPatt patt1 patt2 = memo2 $ \str idx ->
  weave sequentialBinder weaveYieldTransducer (patt1 str idx) $ simpleTransducer (lift >=> patt2 str)

altPatt :: PattCoro -> PattCoro -> PattCoro
altPatt patt1 patt2 = memo2 $ \str idx -> patt1 str idx >>~ patt2 str idx

plusGreedyPatt :: PattCoro -> PattCoro
plusGreedyPatt patt = memo2 $ \str idx -> weave sequentialBinder weaveYieldTransducer (patt str idx) $
  simpleTransducer $ \i -> lift i >>= \i1 -> when (i1 /= idx) (plusGreedyPatt patt str i1) >> yield i

plusLazyPatt :: PattCoro -> PattCoro
plusLazyPatt patt = memo2 $ \str idx -> weave sequentialBinder weaveYieldTransducer (patt str idx) $
  simpleTransducer $ \i -> lift i >>= \i1 -> yield i >> when (i1 /= idx) (plusLazyPatt patt str i1)

plusPatt :: SymBool -> PattCoro -> PattCoro
plusPatt greedy = mrgIf greedy plusGreedyPatt plusLazyPatt

matchFirstWithStartImpl :: PattCoro -> B.ByteString -> Integer -> MaybeT UnionM Integer
matchFirstWithStartImpl patt str startPos = case merge $ pogoStick (\(Yield idx _) -> return $ mrgLift idx) r1 of
  SingleU x -> x
  _ -> error "Should not happen"
  where
    r1 = (\_ -> MaybeT $ return Nothing) <$> patt str startPos

matchFirstImpl :: PattCoro -> B.ByteString -> MaybeT UnionM (Integer, Integer)
matchFirstImpl patt str =
  mrgMsum $ (\s -> (\t -> (s, t - s)) <$> matchFirstWithStartImpl patt str s) <$> [0 .. toInteger $ B.length str]

data ConcPatt
  = ConcPrimPatt B.ByteString
  | ConcSeqPatt ConcPatt ConcPatt
  | ConcAltPatt ConcPatt ConcPatt
  | ConcPlusPatt ConcPatt Bool
  deriving (Show, Generic, ToCon Patt)

data Patt
  = PrimPatt B.ByteString
  | SeqPatt (UnionM Patt) (UnionM Patt)
  | AltPatt (UnionM Patt) (UnionM Patt)
  | PlusPatt (UnionM Patt) SymBool
  deriving (Show, Generic, Eq, Hashable, ToSym ConcPatt, SymEval Model, Mergeable SymBool)

toCoroU :: UnionM Patt -> PattCoro
toCoroU u = getSingle $ mrgFmap toCoro u

toCoroMemoU :: UnionM Patt -> MM.MemoState (MemoHashMap Patt PattCoro) Patt PattCoro PattCoro
toCoroMemoU u = case u of
  SingleU x -> MM.memo toCoroMemo x
  GuardU cond ifTrue ifFalse -> do
    t <- toCoroMemoU ifTrue
    f <- toCoroMemoU ifFalse
    return $ mrgIf cond t f
  _ -> error "Should not happen"

toCoroMemo :: Patt -> MM.MemoState (MemoHashMap Patt PattCoro) Patt PattCoro PattCoro
toCoroMemo (PrimPatt s) = {-trace (show s) $-} return $ primPatt s
toCoroMemo (SeqPatt p1 p2) = do
  p1r <- toCoroMemoU p1
  p2r <- toCoroMemoU p2
  return $ seqPatt p1r p2r
toCoroMemo (AltPatt p1 p2) = do
  p1r <- toCoroMemoU p1
  p2r <- toCoroMemoU p2
  return $ altPatt p1r p2r
toCoroMemo (PlusPatt p greedy) = do
  p1r <- toCoroMemoU p
  return $ plusPatt greedy p1r

toCoro :: Patt -> PattCoro
toCoro x = MM.evalMemoState (toCoroMemo x) emptyMemoHashMap

{-
toCoro :: Patt -> PattCoro
toCoro (PrimPatt s) = getSingle $ mrgFmap primPatt s
toCoro (SeqPatt p1 p2) = seqPatt (toCoroU p1) (toCoroU p2)
toCoro (AltPatt p1 p2) = altPatt (toCoroU p1) (toCoroU p2)
toCoro (PlusPatt p greedy) = plusPatt greedy (toCoroU p)
-}

conformsFirst :: PattCoro -> B.ByteString -> B.ByteString -> SymBool
conformsFirst patt reg str =
  let rp = matchFirstImpl patt str
      rc = bimap toInteger toInteger <$> listToMaybe (getAllMatches (str =~ reg) :: [(Int, Int)])
      rc1 = MaybeT $ mrgReturn rc
   in rp ==~ rc1

synthesisRegexCompiled :: GrisetteSMTConfig b -> UnionM Patt -> PattCoro -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegexCompiled config patt coro reg strs =
  let constraints = conformsFirst coro reg <$> strs
      constraint = foldr (&&~) (conc True) constraints
   in do
        solveRes <- solveWith config constraint
        case solveRes of
          Left _ -> return Nothing
          Right mo -> return $ Just $ symevalToCon mo patt

synthesisRegex :: GrisetteSMTConfig b -> UnionM Patt -> B.ByteString -> [B.ByteString] -> IO (Maybe ConcPatt)
synthesisRegex config patt = synthesisRegexCompiled config patt (toCoroU patt)

test1 :: PattCoro
test1 = toCoro $ toSym $ ConcPrimPatt "a"

reg1 :: B.ByteString
reg1 = "a"

test2 :: PattCoro
test2 = toCoro $ toSym $ ConcSeqPatt (ConcPrimPatt "a") (ConcPrimPatt "b")

reg2 :: B.ByteString
reg2 = "ab"

test3 :: PattCoro
test3 = toCoro $ toSym $ ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")

reg3 :: B.ByteString
reg3 = "a|b"

test4 :: PattCoro
test4 = toCoro $ toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")) True

reg4 :: B.ByteString
reg4 = "(a|b)+"

test5 :: PattCoro
test5 = toCoro $ toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")) False

reg5 :: B.ByteString
reg5 = "(a|b)+?"

test6 :: PattCoro
test6 = toCoro $ toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")) False) (ConcPrimPatt "c")

test7 :: PattCoro
test7 = toCoro $ toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt (ConcPrimPatt "") (ConcPrimPatt "a")) False) (ConcPrimPatt "c")

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
    (choose (toSym $ ConcPrimPatt "a") [toSym $ ConcPrimPatt "b"])
    "a"

freshPrim :: State (Int, String) (UnionM Patt)
freshPrim = choose (toSym $ ConcPrimPatt "d") $ toSym <$> [ConcPrimPatt "c", ConcPrimPatt "b", ConcPrimPatt "a", ConcPrimPatt ""]

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
      (ConcAltPatt (ConcPrimPatt "c") (ConcPrimPatt "d"))
      (ConcPlusPatt (ConcSeqPatt (ConcAltPatt (ConcPrimPatt "") (ConcPrimPatt "a")) (ConcPrimPatt "b")) True)

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
  print sk1
  -}
  res <- time $ synthesisRegex (UnboundedReasoning z3 {transcript = Just "/tmp/a.smt2", timing = PrintTiming}) (mrgSingle sk) "[cd](a?b)+?" $ genWordsUpTo 4 "abcd"
  print res
  print $ matchFirstImpl (toCoro r) "cabab"
  print $ listToMaybe (getAllMatches (("cabab" :: B.ByteString) =~ ("[cd](a?b)+?" :: B.ByteString)) :: [(Int, Int)])
