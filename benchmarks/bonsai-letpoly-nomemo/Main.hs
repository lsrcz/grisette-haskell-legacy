{-# LANGUAGE OverloadedStrings #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import qualified Data.ByteString as B
-- import Data.Foldable
import Data.Maybe
import Grisette
import LetPoly
import Bonsai.SyntaxSpec
import Utils.Timing

testTyperAndEval :: LetPolyTree -> IO ()
testTyperAndEval t = do
  print $ B.append "Testing: " (fromJust $ showConcTree letPolySyntax $ fromJust $toCon t)
  print $
    (fmap . fmap)
      (showConcTree letPolySyntax)
      (toCon $ typer t :: Maybe (Either BonsaiError ConcLetPolyTree))
  print $ eval t

f7 :: UnionM LetPolyTree
f7 = genSym (7 :: Int) "a"

main :: IO ()
main = timeItAll "Overall" $ do
  print $ terminals letPolySyntax
  {-
  print $ typeCompatible intTy intTy
  print $ typeCompatible boolTy boolTy
  print $ typeCompatible intTy anyTy
  print $ typeCompatible boolTy anyTy
  print $ typeCompatible (refTy intTy) (refTy intTy)
  print $ typeCompatible (refTy boolTy) (refTy boolTy)
  print $ typeCompatible (refTy boolTy) anyTy
  print $ typeCompatible (refTy intTy) anyTy
  print $ typeCompatible (arrowTy intTy intTy) (arrowTy intTy intTy)
  print $ typeCompatible (arrowTy intTy intTy) (arrowTy anyTy anyTy)
  putStrLn "Bad: "
  print $ typeCompatible anyTy boolTy
  print $ typeCompatible anyTy intTy
  print $ typeCompatible (refTy anyTy) (refTy intTy)
  print $ typeCompatible (refTy anyTy) (refTy boolTy)
  print $ typeCompatible (refTy intTy) (refTy boolTy)
  print $ typeCompatible (arrowTy anyTy intTy) (arrowTy intTy intTy)
  print $ typeCompatible (arrowTy intTy anyTy) (arrowTy intTy intTy)
  putStrLn "Typer / eval: "

  let toTest =
        [ oneTerm,
          trueTerm,
          opTerm "-" oneTerm,
          opTerm "!" trueTerm,
          opTerm "&" oneTerm,
          opTerm "&" trueTerm,
          opTerm "*" (opTerm "&" trueTerm),
          letTerm "a" trueTerm (nameTerm "a"),
          letTerm "a" (opTerm "&" trueTerm) (nameTerm "a"),
          letTerm
            "a"
            (opTerm "&" trueTerm)
            (assignTerm (nameTerm "a") (opTerm "!" trueTerm) (opTerm "*" (nameTerm "a"))),
          assignTerm (opTerm "&" trueTerm) trueTerm (opTerm "&" trueTerm),
          opTerm "&" $ opTerm "&" trueTerm,
          opTerm "*" $ opTerm "&" $ opTerm "&" trueTerm,
          assignTerm (opTerm "&" $ opTerm "&" trueTerm) (opTerm "&" trueTerm) (opTerm "&" trueTerm),
          letTerm "a" (opTerm "&" trueTerm) (opTerm "&" $ nameTerm "a"),
          letTerm "e" (opTerm "&" $ opTerm "!" trueTerm) $
            assignTerm (nameTerm "e") oneTerm oneTerm,
          opTerm "*" $ opTerm "*" $ opTerm "&" $ opTerm "&" trueTerm,
          letTerm "a" (opTerm "&" $ lambdaTerm "e" anyTy (nameTerm "e")) $
            assignTerm (nameTerm "a") (nameTerm "a") $
              nameTerm "a",
          letTerm "a" (opTerm "&" $ lambdaTerm "e" anyTy (nameTerm "e")) $
            opTerm "*" $ opTerm "&" (nameTerm "a"),
          letTerm "a" (opTerm "&" $ lambdaTerm "a" anyTy (nameTerm "a")) $
            assignTerm (nameTerm "a") (lambdaTerm "a" boolTy $ opTerm "!" (nameTerm "a")) $
              callTerm (opTerm "*" $ nameTerm "a") oneTerm,
          opTerm "*" $ opTerm "&" trueTerm
        ]
  traverse_ testTyperAndEval toTest
  -}

  --print f7
  --print $ matchLetPolySyntax #~ f7 # "term"
  --print $ mrgFmap (const ()) $ typer #~ f7
  --print $ mrgFmap (const ()) $ eval #~ f7
  let result = lift f7 >>= execLetPoly
  _ <- timeItAll "evaluate" $ runExceptT result `deepseq` return ()
  r <- timeItAll "lower/solve" $ solveWithTranslation VerifyTyper (BoundedReasoning @7 boolector {verbose = False}) result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree letPolySyntax <$> (toCon $ evaluate True mo f7 :: Maybe ConcLetPolyTree)
      print $ evaluate True mo result
      print $ evaluate False mo f7
      print $ evaluate True mo (lift f7) >>= execLetPoly
