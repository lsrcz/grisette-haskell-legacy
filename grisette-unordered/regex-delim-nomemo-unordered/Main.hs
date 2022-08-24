{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Main where

import Control.Monad.Cont
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe
import Control.Natural
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Proxy
import Grisette
import Grisette.Unordered.UUnionM
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

type CoroBase a = ContT (Thread UUnionM (UUnionM Int)) UUnionM a

type CoroReset = CoroBase (Thread UUnionM (UUnionM Int))

type Coro = CoroBase ()

type PattCoroReset = B.ByteString -> Int -> CoroReset

pipe :: CoroReset -> (UUnionM Int -> Coro) -> Coro
pipe c f = mrgResetT c >>= foldThread lift (return ()) (\x r -> f x >> r)
{-# INLINE pipe #-}

callCoro :: CoroReset -> Coro
callCoro c = pipe c yield

delimitCoro :: Coro -> CoroReset
delimitCoro = mrgResetT . (Done <$)

primPatt :: Char -> PattCoroReset
primPatt pattc str idx =
  delimitCoro $
    when (B.length str > idx && C.index str idx == pattc) $
      yield (mrgReturn $ idx + 1)

seqPatt :: PattCoroReset -> PattCoroReset -> PattCoroReset
seqPatt patt1 patt2 str idx = delimitCoro $ pipe (patt1 str idx) (lift >=> callCoro . patt2 str)

altPatt :: PattCoroReset -> PattCoroReset -> PattCoroReset
altPatt patt1 patt2 str idx = delimitCoro $ callCoro (patt1 str idx) >> callCoro (patt2 str idx)

emptyPatt :: PattCoroReset
emptyPatt str idx =
  delimitCoro $ when (B.length str >= idx) (yield $ mrgReturn idx)

plusPatt :: PattCoroReset -> SymBool -> PattCoroReset
plusPatt patt greedy str idx =
  delimitCoro . pipe (patt str idx) $
    lift >=> \i ->
      mrgIf
        greedy
        (when (i /= idx) (callCoro (plusPatt patt (conc True) str i)) >> yield (mrgReturn i))
        (yield (mrgReturn i) >> when (i /= idx) (callCoro (plusPatt patt (conc False) str i)))

data RegexDelimNomemo

instance RegexSynth RegexDelimNomemo where
  type PattCoroType RegexDelimNomemo = PattCoroReset
  toCoro tag = \case
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
main = timeItAll "Overall" $ regexMain (Proxy @RegexDelimNomemo)
