{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Main where

import STLC
import Grisette.Core
import Grisette.SymPrim.Term
import BonsaiTree
import Match
import Error
import Pattern
import Control.Monad.Trans
import SyntaxSpec
import Grisette.Backend.SBV
import Control.DeepSeq
import Utils.Timing
import Control.Monad.Except

x1 :: BonsaiTree 14
x1 = BonsaiNode (mrgGuard "cond" (mrgSingle (simpleNode "call")) (mrgSingle $ simpleNode "+"))
       (uBonsaiNode (mrgSingle $ simpleNode "+") (mrgSingle $ simpleNode "one"))

f1 :: UnionM (BonsaiTree 14)
f1 = genSym (1 :: Int) "a"
f2 :: UnionM (BonsaiTree 14)
f2 = genSym (2 :: Int) "b"
f3 :: UnionM (BonsaiTree 14)
f3 = genSym (3 :: Int) "c"
f5 :: UnionM (BonsaiTree 14)
f5 = genSym (5 :: Int) "e"
f8 :: UnionM (BonsaiTree 14)
f8 = genSym (8 :: Int) "h"

main :: IO ()
main = do
  print $ terminals stlcSyntax
  print $ matchStlcSyntax x1 "term"
  print f1
  print f2
  print f3
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    placeHolder ==> mrgLift
    ] #~ f1
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    literal "+" ==> mrgReturn (1 :: Integer)
    ] #~ f1
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    placeHolder *= placeHolder ==> (\a _ -> mrgLift a)
    ] #~ f1
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    literal "+" ==> mrgReturn (1 :: Integer)
    ] #~ f2
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    placeHolder *= placeHolder ==> (\a _ -> mrgLift a)
    ] #~ f2
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    literal "+" *= placeHolder ==> lift
    ] #~ f3
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    literal "cons" *= (literal "one" *= literal "nil") ==> mrgReturn (1 :: Integer)
    ] #~ f3
  print $ bonsaiMatchCustomError BonsaiTypeError stlcSyntax [
    literal "a" ==> mrgReturn (1 :: Integer),
    literal "b" ==> mrgReturn (2 :: Integer)
    ] #~ f3
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer oneNode  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer nilNode  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (simpleNode "cons")  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (simpleNode "hd")  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (simpleNode "tl")  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (simpleNode "+")  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (simpleNode "a")  :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (lambdaNode "a" intTy (simpleNode "a"))
       :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (lambdaNode "a" intTy (simpleNode "b"))
       :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (callNode (simpleNode "+") (simpleNode "one"))
       :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (callNode (simpleNode "+") (simpleNode "one"))
       :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print ((fmap . fmap) (showConcTree stlcSyntax)
    (toCon $ typer (callNode (lambdaNode "a" intTy (simpleNode "a")) (simpleNode "one"))
       :: Maybe (Either BonsaiError (ConcBonsaiTree 14))))
  print $ interpreter oneNode
  print $ interpreter nilNode
  print $ interpreter (simpleNode "cons")
  print $ interpreter (callNode (simpleNode "cons") oneNode)
  print $ interpreter (consNode oneNode nilNode)
  print $ interpreter (simpleNode "+")
  print $ interpreter (callNode (simpleNode "+") oneNode)
  print $ interpreter (plusNode oneNode oneNode)
  print $ interpreter (hdNode nilNode)
  print $ interpreter (tlNode nilNode)
  print $ interpreter (hdNode $ consNode (plusNode oneNode oneNode) nilNode)
  print $ interpreter (tlNode $ consNode oneNode $ consNode (plusNode oneNode oneNode) nilNode)
  print $ interpreter (callNode (lambdaNode "a" intTy (lambdaNode "b" intTy (simpleNode "a"))) oneNode)
  print $ interpreter (callNode (callNode
    (lambdaNode "a" intTy (lambdaNode "b" intTy (simpleNode "a"))) oneNode) (plusNode oneNode oneNode))
  print $ interpreter (callNode (lambdaNode "a" intTy (lambdaNode "a" intTy (simpleNode "a"))) oneNode)
  print $ interpreter (callNode (callNode
    (lambdaNode "a" intTy (lambdaNode "a" intTy (simpleNode "a"))) oneNode) (plusNode oneNode oneNode))

  let result = lift f8 >>= execStlc
  _ <- timeItAll "symeval" $ runExceptT result `deepseq` return ()
  r <- timeItAll "lower/solve" $ solveWithTranslation VerifyTyper (BoundedReasoning @6 z3) result 
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree stlcSyntax <$> (toCon $ symeval True mo f8 :: Maybe (ConcBonsaiTree 14))
