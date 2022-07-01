{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import Grisette
-- import Bonsai.Match
-- import Bonsai.Pattern
import STLC
-- import Bonsai.SyntaxSpec
import Utils.Timing

f8 :: UnionM STLCTree
f8 = genSym (8 :: Int) "h"

main :: IO ()
main = timeItAll "Overall" $ do
  let result = lift f8 >>= execStlc
  _ <- timeItAll "evaluate" $ runExceptT result `deepseq` return ()
  r <- timeItAll "Lowering/Solving" $ solveWithExcept VerifyTyper (BoundedReasoning @6 boolector) result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree stlcSyntax <$> (toCon $ evaluate True mo f8 :: Maybe (ConcSTLCTree))
