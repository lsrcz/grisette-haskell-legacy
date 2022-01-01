{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Functor.Sum
import Grisette.Control.Monad
import Grisette.Control.Monad.Trans
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.UnionOp
import Grisette.Data.Functor
import qualified Data.ByteString as B
import Grisette.Data.SymPrim
import GHC.Generics
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.ToCon
import Text.Regex.PCRE
import Data.Maybe

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
    map' (Right r) = Right r
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
primPatt pattstr str idx =
  when (idx + toInteger (B.length pattstr) <= toInteger (B.length str) && pattstr == B.take (B.length pattstr) (B.drop (fromInteger idx) str)) $
    yield $ mrgReturn $ idx + toInteger (B.length pattstr)

seqPatt :: PattCoro -> PattCoro -> PattCoro
seqPatt patt1 patt2 str idx =
  weave sequentialBinder weaveYieldTransducer (patt1 str idx) $ simpleTransducer (lift >=> patt2 str)

altPatt :: PattCoro -> PattCoro -> PattCoro
altPatt patt1 patt2 str idx = patt1 str idx >>~ patt2 str idx

plusGreedyPatt :: PattCoro -> PattCoro
plusGreedyPatt patt str idx = weave sequentialBinder weaveYieldTransducer (patt str idx) $
  simpleTransducer $ \i -> lift i >>= \i1 -> when (i1 /= idx) (plusGreedyPatt patt str i1) >> yield i

plusLazyPatt :: PattCoro -> PattCoro
plusLazyPatt patt str idx = weave sequentialBinder weaveYieldTransducer (patt str idx) $
  simpleTransducer $ \i -> lift i >>= \i1 -> yield i >> when (i1 /= idx) (plusLazyPatt patt str i1)

plusPatt :: SymBool -> PattCoro -> PattCoro
plusPatt greedy = mrgIf greedy plusGreedyPatt plusLazyPatt

matchFirstWithStartImpl :: PattCoro -> B.ByteString -> Integer -> MaybeT UnionM Integer
matchFirstWithStartImpl patt str startPos = case merge $ pogoStick (\(Yield idx _) -> return $ mrgLift idx) r of
  SingleU x -> x
  _ -> error "Should not happen"
  where
    r = (\_ -> MaybeT $ return Nothing) <$> patt str startPos

matchFirstImpl :: PattCoro -> B.ByteString -> MaybeT UnionM (Integer, Integer)
matchFirstImpl patt str =
  mrgMsum $ (\s -> (\t -> (s, t - s)) <$> matchFirstWithStartImpl patt str s) <$> [0 .. toInteger $ B.length str]

data ConcPatt
  = ConcPrimPatt B.ByteString
  | ConcSeqPatt ConcPatt ConcPatt
  | ConcAltPatt ConcPatt ConcPatt
  | ConcPlusPatt ConcPatt Bool
  deriving (Show, Generic)
 
data Patt
  = PrimPatt (UnionM B.ByteString)
  | SeqPatt (UnionM Patt) (UnionM Patt)
  | AltPatt (UnionM Patt) (UnionM Patt)
  | PlusPatt (UnionM Patt) SymBool
  deriving (Show, Generic)

instance Mergeable (Sym Bool) Patt
instance ToSym ConcPatt Patt
instance ToCon Patt ConcPatt

toCoroU :: UnionM Patt -> PattCoro
toCoroU u = getSingle $ mrgFmap toCoro u

toCoro :: Patt -> PattCoro
toCoro (PrimPatt s) = getSingle $ mrgFmap primPatt s
toCoro (SeqPatt p1 p2) = seqPatt (toCoroU p1) (toCoroU p2)
toCoro (AltPatt p1 p2) = altPatt (toCoroU p1) (toCoroU p2)
toCoro (PlusPatt p greedy) = plusPatt greedy (toCoroU p)

test1 = toCoro $ toSym $ ConcPrimPatt "a"

reg1 :: B.ByteString
reg1 = "a"

test2 = toCoro $ toSym $ ConcSeqPatt (ConcPrimPatt "a") (ConcPrimPatt "b")

reg2 :: B.ByteString
reg2 = "ab"

test3 = toCoro $ toSym $ ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")

reg3 :: B.ByteString
reg3 = "a|b"

test4 = toCoro $ toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")) True

reg4 :: B.ByteString
reg4 = "(a|b)+"

test5 = toCoro $ toSym $ ConcPlusPatt (ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")) False

reg5 :: B.ByteString
reg5 = "(a|b)+?"

test6 = toCoro $ toSym $ ConcSeqPatt (ConcPlusPatt (ConcAltPatt (ConcPrimPatt "a") (ConcPrimPatt "b")) False) (ConcPrimPatt "c")

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

main :: IO ()
main = do
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
