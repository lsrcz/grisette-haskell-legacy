{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.Monad
import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Proxy
import Grisette
import Grisette.Unordered.UUnionM
import Regex
import Transducer
import Utils.Timing

-- The type for a pattern coroutine.
-- The first argument is the string to match.
-- The second argument is start position to match the current pattern.
-- The yielded values are the positions after the last matched character.
type PattCoro = B.ByteString -> Int -> Coroutine (Yield (UUnionM Int)) UUnionM ()

-- Compiling the patterns.
-- htmemo* are memoizer implementation bundled with Grisette.
-- They are implemented with HashTables
primPatt :: Char -> PattCoro
primPatt pattc = htmemo2 $ \str idx ->
  when (B.length str > idx && C.index str idx == pattc) $
    yield $
      mrgReturn $
        idx + 1

seqPatt :: PattCoro -> PattCoro -> PattCoro
seqPatt patt1 patt2 = htmemo2 $ \str idx ->
  patt1 str idx |>>= (lift >=> patt2 str)

altPatt :: PattCoro -> PattCoro -> PattCoro
altPatt patt1 patt2 = htmemo2 $ \str idx -> patt1 str idx >> patt2 str idx

emptyPatt :: PattCoro
emptyPatt str idx = when (B.length str >= idx) $ yield $ mrgReturn idx

plusPatt :: PattCoro -> SymBool -> PattCoro
plusPatt patt =
  fix $
    htmemo3 . \f greedy str idx ->
      patt str idx
        |>>= ( lift >=> \i1 ->
                 mrgIf
                   greedy
                   (when (i1 /= idx) (f (conc True) str i1) >> yield (mrgReturn i1))
                   (yield (mrgReturn i1) >> when (i1 /= idx) (f (conc False) str i1))
             )

data RegexFree

instance RegexSynth RegexFree where
  type PattCoroType RegexFree = PattCoro

  toCoro tag = htmemo $ \case
    PrimPatt s -> primPatt s
    SeqPatt p1 p2 -> seqPatt (toCoroU tag p1) (toCoroU tag p2)
    AltPatt p1 p2 -> altPatt (toCoroU tag p1) (toCoroU tag p2)
    PlusPatt subp greedy -> plusPatt (toCoroU tag subp) greedy
    EmptyPatt -> emptyPatt
  {-# INLINE toCoro #-}

  matchFirstWithStart _ patt str startPos = case merge $ pogoStick (\(Yield idx _) -> return $ mrgLift idx) r1 of
    SingleU x -> x
    _ -> error "Should not happen"
    where
      r1 = (\_ -> MaybeT $ return Nothing) <$> patt str startPos
  {-# INLINE matchFirstWithStart #-}

main :: IO ()
main = timeItAll "Overall" $ regexMain (Proxy @RegexFree)
