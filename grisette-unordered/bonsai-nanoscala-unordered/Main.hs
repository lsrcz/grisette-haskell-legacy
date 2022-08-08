{-# LANGUAGE OverloadedStrings #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import Grisette
import NanoScala
import Utils.Timing
import Grisette.Unordered.UUnionM

f10 :: UUnionM DotTree
f10 = genSym (10 :: Int) "a"

main :: IO ()
main = timeItAll "Overall" $ do
  let result = runExceptT $ lift f10 >>= execDot
  _ <- timeItAll "evaluate" $ result `deepseq` return ()
  r <- timeItAll "Lowering/Solving" $ solve VerifyTyper (BoundedReasoning @6 boolector) result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree dotSyntax <$> (toCon $ evaluate True mo f10 :: Maybe ConcDotTree)
