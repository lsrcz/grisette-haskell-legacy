{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import Grisette
import Grisette.Unordered.UUnionM
import STLC
import Utils.Timing

f8 :: UUnionM STLCTree
f8 = genSym (8 :: Int) "h"

main :: IO ()
main = timeItAll "Overall" $ do
  let result = runExceptT $ lift f8 >>= execStlc
  _ <- timeItAll "evaluate" $ result `deepseq` return ()
  r <- timeItAll "Lowering/Solving" $ solveFallable (BoundedReasoning @6 boolector) verifyTyperTranslation result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree stlcSyntax <$> (toCon $ evaluate True mo f8 :: Maybe (ConcSTLCTree))
