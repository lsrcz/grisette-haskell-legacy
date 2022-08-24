{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Main where

import Control.Monad.Cont
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe
import Control.Natural
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Function (fix)
import Data.Proxy
import Grisette
import Regex
import Utils.Timing

data Thread m a = Done | Resume a (m (Thread m a))

foldThread :: Monad rm => (m ~> rm) -> rm r -> (a -> rm r -> rm r) -> Thread m a -> rm r
foldThread _ done _ Done = done
foldThread nt done resume (Resume x m) = resume x (nt m >>= foldThread nt done resume)
{-# INLINE foldThread #-}

yield :: (Monad m) => a -> ContT (Thread m a) m ()
yield x = shiftT (\k -> return $ Resume x (k ()))

instance (Mergeable1 bool m, Mergeable bool a) => Mergeable bool (Thread m a) where
  mergingStrategy =
    SortedStrategy
      (\case Done -> False; Resume {} -> True)
      ( \case
          False -> SimpleStrategy $ \_ t _ -> t
          True -> product2Strategy Resume (\(Resume l r) -> (l, r)) mergingStrategy mergingStrategy1
      )

type CoroBase a = ContT (Thread UnionM (UnionM Int)) UnionM a

type CoroReset = CoroBase (Thread UnionM (UnionM Int))

type Coro = CoroBase ()

type PattCoroReset = B.ByteString -> Int -> CoroReset

pipe :: CoroReset -> (UnionM Int -> Coro) -> Coro
pipe c f = mrgResetT c >>= foldThread lift (return ()) (\x r -> f x >> r)
{-# INLINE pipe #-}

callCoro :: CoroReset -> Coro
callCoro c = pipe c yield

delimitCoro :: Coro -> CoroReset
delimitCoro = mrgResetT . (Done <$)

primPatt :: Char -> PattCoroReset
primPatt pattc = htmemo2 $ \str idx ->
  delimitCoro $
    when (B.length str > idx && C.index str idx == pattc) $
      yield (mrgReturn $ idx + 1)

seqPatt :: PattCoroReset -> PattCoroReset -> PattCoroReset
seqPatt patt1 patt2 = htmemo2 $ \str idx -> delimitCoro $ pipe (patt1 str idx) (lift >=> callCoro . patt2 str)

altPatt :: PattCoroReset -> PattCoroReset -> PattCoroReset
altPatt patt1 patt2 = htmemo2 $ \str idx -> delimitCoro $ callCoro (patt1 str idx) >> callCoro (patt2 str idx)

emptyPatt :: PattCoroReset
emptyPatt = htmemo2 $ \str idx ->
  delimitCoro $ when (B.length str >= idx) (yield $ mrgReturn idx)

plusPatt :: PattCoroReset -> SymBool -> PattCoroReset
plusPatt patt =
  fix $
    htmemo3 . \f greedy str idx ->
      delimitCoro . pipe (patt str idx) $
        lift >=> \i1 ->
          mrgIf
            greedy
            (when (i1 /= idx) (callCoro (f (conc True) str i1)) >> yield (mrgReturn i1))
            (yield (mrgReturn i1) >> when (i1 /= idx) (callCoro (f (conc False) str i1)))

data RegexDelim

instance RegexSynth RegexDelim where
  type PattCoroType RegexDelim = PattCoroReset
  toCoro tag = htmemo $ \case
    PrimPatt s -> primPatt s
    SeqPatt p1 p2 -> seqPatt (toCoroU tag p1) (toCoroU tag p2)
    AltPatt p1 p2 -> altPatt (toCoroU tag p1) (toCoroU tag p2)
    PlusPatt subp greedy -> plusPatt (toCoroU tag subp) greedy
    EmptyPatt -> emptyPatt
  {-# INLINE toCoro #-}

  matchFirstWithStart _ patt str startPos =
    MaybeT $
      mrgEvalContT (patt str startPos)
        >>= foldThread id (mrgReturn Nothing) (const . mrgFmap Just)
  {-# INLINE matchFirstWithStart #-}

main :: IO ()
main = timeItAll "Overall" $ regexMain (Proxy @RegexDelim)
