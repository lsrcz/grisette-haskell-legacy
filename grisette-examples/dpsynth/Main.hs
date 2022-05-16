{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad.Except
import Grisette
import Test.QuickCheck hiding (choose, verbose)
import Utils.Timing
import Core
import Ops
import MAS
import MIS
import MMM
import MSS
import Data.Maybe
import Debug.Trace



main :: IO ()
main = do
  let config = UnboundedReasoning z3 {timing=PrintTiming}
  let configb = UnboundedReasoning boolector {timing=PrintTiming} -- {verbose=True, transcript=Just "/tmp/a.smt2"}
  -- let config1 = BoundedReasoning @5 z3
  --print (mis @Integer)
  --quickCheck $ \(x :: [Integer]) -> interpretSketch @SymInteger availableUnary availableBinary (toSym $ mis @Integer) (toSym $ (: []) <$> x) == mrgReturn (toSym $ misAlgo x)

{-
  misIntSynthed1 :: Maybe (ConProgram Integer) <-
    timeItAll "mis" $ synth1 config availableUnary availableBinary () (const $ conc True) (misSpec @Integer . fmap (getSingle . head)) misSketch
  print misIntSynthed1
  misIntSynthedOpt :: Maybe (ConProgram Integer) <-
    timeItAll "misopt" $ synth1 config availableUnary availableBinary () (const $ conc True) (misSpec @Integer . fmap (getSingle . head)) misSketchOpt
  print misIntSynthedOpt

  --print (mss @Integer)
  --quickCheck $ \(x :: [Integer]) -> interpretSketch @SymInteger availableUnary availableBinary (toSym $ mss @Integer) (toSym $ (: []) <$> x) == mrgReturn (toSym $ mssAlgo2 x)

  mssIntSynthed1 :: Maybe (ConProgram Integer) <-
    timeItAll "mss" $ synth1 config availableUnary availableBinary () (const $ conc True) (mssSpec @Integer . fmap (getSingle . head)) mssSketch
  print mssIntSynthed1
  -}

{-
  --print (mas @Integer)
  --quickCheck $ \(x :: [Integer]) -> interpretSketch @SymInteger availableUnary availableBinary (toSym $ mas @Integer) (toSym $ (: []) <$> x) == mrgReturn (toSym $ masAlgo x)

  masIntSynthedV :: Maybe (ConProgram Integer) <-
    timeItAll "masV" $ synth1 config availableUnary availableBinary () (const $ conc True) (masSpec @Integer . fmap (getSingle . head)) (toSym (mas @Integer))
  print masIntSynthedV
  -}

  quickCheck $ \(x :: [Integer]) -> interpretSketch @SymInteger availableUnary availableBinary (toSym $ masSynthed1 @Integer) (toSym $ (: []) <$> x) == mrgReturn (toSym $ masAlgo x)
  quickCheck $ \(x :: [Integer]) -> interpretSketch @SymInteger availableUnary availableBinary (toSym $ masSynthedOpt1 @Integer) (toSym $ (: []) <$> x) == mrgReturn (toSym $ masAlgo x)


  masIntSynthedOpt1 :: Maybe (ConProgram (SignedBV 11)) <-
    timeItAll "masOpt1" $ synth1 configb availableUnary availableBinary ()
       (\x -> let t = foldl (\acc y -> acc &&~ y >=~ -8 &&~ y <=~ 8) (conc True) $ getSingle <$> join x in trace (show t) t) (masSpec @(SignedBV 11) . fmap (getSingle . head)) masSketchOpt
  print masIntSynthedOpt1
  print $ interpretSketch @(SymSignedBV 11) availableUnary availableBinary (toSym $ fromJust masIntSynthedOpt1) ((: []) <$> [-1,1,1,-2])
  print $ interpretSketch @(SymSignedBV 11) availableUnary availableBinary (toSym $ masSynthedOpt1 @(SignedBV 11)) ((: []) <$> [-1,1,1,-2])

{-
  masIntSynthedOpt :: Maybe (ConProgram Integer) <-
    timeItAll "masOpt" $ synth1 config availableUnary availableBinary ()
       (const $ conc True) (masSpec @Integer . fmap (getSingle . head)) masSketchOpt
  print masIntSynthedOpt
  -}

  masIntSynthed1 :: Maybe (ConProgram (SignedBV 10)) <-
    timeItAll "mas1" $ synth1 configb availableUnary availableBinary ()
       (\x -> foldl (\acc y -> acc &&~ y >=~ -4 &&~ y <=~ 4) (conc True) $ getSingle <$> join x) (masSpec @(SignedBV 10) . fmap (getSingle . head)) masSketch
  print masIntSynthed1

  masIntSynthed1' :: Maybe (ConProgram (SignedBV 10)) <-
    timeItAll "mas1'" $ synth1 configb availableUnary availableBinary ()
       (\x -> foldl (\acc y -> acc &&~ y >=~ -4 &&~ y <=~ 4) (conc True) $ getSingle <$> join x) (masSpec @(SignedBV 10) . fmap (getSingle . head)) masSketch1
  print masIntSynthed1'

  masIntSynthed :: Maybe (ConProgram Integer) <-
    timeItAll "mas" $ synth1 config availableUnary availableBinary () (const $ conc True) (masSpec @Integer . fmap (getSingle . head)) masSketch
  print masIntSynthed



-- mssSynthed <- synth config [["a"], ["b"], ["c"], ["d"]] (const $ conc True) (mssSpec . fmap head) (toSym mss)
-- print mssSynthed
{-
print mas
quickCheck $ \(x :: [Integer]) -> interpretIntSketch (toSym mas) (toSym $ (: []) <$> x) == mrgReturn (toSym $ masAlgo x)
print mmm
quickCheck $ \(x :: [Integer]) -> interpretIntSketch (toSym mmm) (toSym $ (: []) <$> x) == mrgReturn (toSym $ mmmAlgo x)
print assem
quickCheck $ \(x :: [(Integer, Integer)]) ->
  interpretIntSketch (toSym assem) (toSym $ (\(stay, switch) -> [stay, switch]) <$> x)
    == mrgReturn (toSym $ assemAlgo x)
    -}

{-
synth :: GrisetteSMTConfig n -> [[SymInteger]] -> ([[SymInteger]] -> SymBool) -> ([[SymInteger]] -> SymInteger) -> Program SymInteger -> IO (Maybe (ConProgram Integer))
synth config inputs inputSpace spec sketch = do
  -}