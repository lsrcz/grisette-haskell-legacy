{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Char8 as C
import Data.Proxy
import Grisette
import Regex
import Transducer
import Utils.Timing

type PattCoro = B.ByteString -> Int -> Coroutine (Yield (UnionM Int)) UnionM ()

primPatt :: Char -> PattCoro
primPatt pattc str idx =
  when (B.length str > idx && C.index str idx == pattc) $
    yield $
      mrgReturn $
        idx + 1

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

data RegexFreeNomemo

instance RegexSynth RegexFreeNomemo where
  type PattCoroType RegexFreeNomemo = PattCoro

  matchFirstWithStart _ patt str startPos = case merge $ pogoStick (\(Yield idx _) -> return $ mrgLift idx) r1 of
    SingleU x -> x
    _ -> error "Should not happen"
    where
      r1 = (\_ -> MaybeT $ return Nothing) <$> patt str startPos
  {-# INLINE matchFirstWithStart #-}

  toCoro tag = \case
    PrimPatt s -> primPatt s
    SeqPatt p1 p2 -> seqPatt (toCoroU tag p1) (toCoroU tag p2)
    AltPatt p1 p2 -> altPatt (toCoroU tag p1) (toCoroU tag p2)
    PlusPatt subp greedy -> plusPatt (toCoroU tag subp) greedy
    EmptyPatt -> emptyPatt
  {-# INLINE toCoro #-}

main :: IO ()
main = timeItAll "Overall" $ regexMain (Proxy @RegexFreeNomemo)
