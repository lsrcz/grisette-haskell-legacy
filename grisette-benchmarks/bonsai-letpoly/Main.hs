{-# LANGUAGE OverloadedStrings #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import Grisette
import LetPoly
import Utils.Timing

f7 :: UnionM LetPolyTree
f7 = genSym (7 :: Int) "a"

main :: IO ()
main = timeItAll "Overall" $ do
  let result = lift f7 >>= execLetPoly
  _ <- timeItAll "evaluate" $ runExceptT result `deepseq` return ()
  r <- timeItAll "Lowering/Solving" $ solveWithExcept VerifyTyper (BoundedReasoning @7 boolector {verbose = False}) result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree letPolySyntax <$> (toCon $ evaluate True mo f7 :: Maybe ConcLetPolyTree)
      print $ evaluate True mo result
      print $ evaluate False mo f7
      print $ evaluate True mo (lift f7) >>= execLetPoly
