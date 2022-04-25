{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.Except
import Control.Monad.Writer
import GHC.Generics
import GHC.IO.Unsafe
import Grisette

newtype ConTrace = ConTrace [(Integer, Integer)]
  deriving (Show, Generic)
  deriving (ToCon Trace) via (Default ConTrace)

newtype Trace = Trace (UnionM [(SymInteger, SymInteger)])
  deriving (Show, Generic)
  deriving (Mergeable SymBool, Evaluate Model, ToSym ConTrace, SEq SymBool) via (Default Trace)

instance Semigroup Trace where
  Trace l <> Trace r = Trace $ do
    l1 <- l
    r1 <- r
    mrgReturn $ l1 ++ r1

instance Monoid Trace where
  mempty = Trace $ mrgReturn []

type M = GenSymFreshT (WriterT Trace (ExceptT AssertionError UnionM))

swap ::
  (MonadError AssertionError m, MonadUnion SymBool m, Mergeable SymBool x) =>
  [x] ->
  SymInteger ->
  SymInteger ->
  m [x]
swap l x y =
  mrgIf (x <=~ y) (go l x y) (go l y x)
  where
    go [] _ _ = mrgThrowError AssertionError
    go r@(v : vs) x1 y1 = mrgIf (x1 ==~ 0) (mrgIf (y1 ==~ 0) (mrgReturn r) (go1 v vs y1)) (mrgFmap (v :) $ go vs (x1 - 1) (y1 - 1))
    go1 v l1 y1 = do
      (v', r) <- go2 v l1 (y1 - 1)
      mrgReturn $ v' : r
    go2 _ [] _ = mrgThrowError AssertionError
    go2 v (v1 : v1s) y1 =
      mrgIf
        (y1 ==~ 0)
        (mrgReturn (v1, v : v1s))
        ( do
            (v', r) <- go2 v v1s (y1 - 1)
            mrgReturn (v', v1 : r)
        )

type Algo = forall x. (Mergeable SymBool x) => Integer -> [x] -> M [x]

algo0 :: Algo
algo0 fuel l
  | fuel < 0 = mrgThrowError AssertionError
  | otherwise = do
    c <- genSymSimpleFresh @SymBool ()
    mrgIf
      c
      ( do
          i <- genSymSimpleFresh @SymBool ()
          j <- genSymSimpleFresh @SymBool ()
          r <- swap l i j
          lift . tell $ Trace $ mrgReturn [(i, j)]
          algo0 (fuel - 1) r
      )
      ( mrgReturn l
      )

algo1 :: Algo
algo1 fuel = go fuel 0
  where
    go fuel1 i l
      | fuel1 < 0 = mrgReturn l
      | otherwise = do
        c <- genSymSimpleFresh @SymBool ()
        mrgIf
          c
          ( do
              j <- genSymSimpleFresh @SymBool ()
              r <- swap l (conc i) j
              lift . tell $ Trace $ mrgReturn [(conc i, j)]
              go (fuel1 - 1) (i + 1) r
          )
          (mrgReturn l)

data Marble = Red | White | Blue
  deriving (Generic, Show, Eq)
  deriving (Mergeable SymBool, SEq SymBool, ToSym Marble) via Default Marble

data DutchFlag = DutchFlag {nred :: Int, nwhite :: Int}

instance SolverTranslation DutchFlag AssertionError ([UnionM Marble], Trace) where
  errorTranslation _ _ = False
  valueTranslation (DutchFlag r w) (v, _) =
    isColor Red rmarbles &&~ isColor White wmarbles &&~ isColor Blue bmarbles
    where
      rmarbles = take r v
      wmarbles = take w $ drop r v
      bmarbles = drop (r + w) v
      isColor :: Marble -> [UnionM Marble] -> SymBool
      isColor m = foldl (\acc n -> acc &&~ mrgReturn m ==~ n) (conc True)

-- This one is lazy. But it does not perform incremental reasoning and can be slow.
runDutchFlag :: GrisetteSMTConfig n -> Algo -> Integer -> [Marble] -> IO [ConTrace]
runDutchFlag config algo len initMarbles = do
  initialResult <- solveProb final
  case initialResult of
    Nothing -> return []
    Just ct -> do
      r <- unsafeInterleaveIO $ go final ct
      return $ ct : r
  where
    solveProb result = do
      ms <- solveWithTranslation (DutchFlag (length $ filter (== Red) initMarbles) (length $ filter (== White) initMarbles)) config result
      case ms of
        Left _ -> return Nothing
        Right mo -> do
          let res :: Either AssertionError ConTrace = evaluateToCon mo (runExceptT (snd <$> result) :: UnionM (Either AssertionError Trace))
          case res of
            Left _ -> error "Bad"
            Right ct -> return $ Just ct
    final = runWriterT (runGenSymFreshT (algo len (toSym initMarbles)) "a")
    go result lastResult = do
      let newresult = do
            (m, r) <- result
            symAssert $ r /=~ toSym lastResult
            return (m, r)
      next <- solveProb newresult
      case next of
        Nothing -> return []
        Just ct -> do
          remaining <- unsafeInterleaveIO $ go newresult ct
          return $ ct : remaining

-- It's a pity that solveMultiWithTranslation is not lazy.
-- We currently cannot do this lazily due to the restriction of SBV APIs.
runDutchFlag' :: GrisetteSMTConfig n -> Algo -> Integer -> Int -> [Marble] -> IO [ConTrace]
runDutchFlag' config algo len maxModelCnt initMarbles = do
  ms <- solveMultiWithTranslation (DutchFlag (length $ filter (== Red) initMarbles) (length $ filter (== White) initMarbles)) config maxModelCnt final
  return $
    ( \mo ->
        let res :: Either AssertionError ConTrace = evaluateToCon mo (runExceptT (snd <$> final) :: UnionM (Either AssertionError Trace))
         in case res of
              Left _ -> error "Bad"
              Right ct -> ct
    )
      <$> ms
  where
    final = runWriterT (runGenSymFreshT (algo len (toSym initMarbles)) "a")

main :: IO ()
main = do
  let config = UnboundedReasoning z3 --{verbose=True}
  runDutchFlag config algo0 3 [Blue, White, Red, White, Red, White, Blue] >>= print . take 3
  runDutchFlag config algo1 7 [Blue, White, Red, White, Red, White, Blue] >>= print . take 3
  runDutchFlag' config algo0 3 3 [Blue, White, Red, White, Red, White, Blue] >>= print
  runDutchFlag' config algo1 7 3 [Blue, White, Red, White, Red, White, Blue] >>= print

