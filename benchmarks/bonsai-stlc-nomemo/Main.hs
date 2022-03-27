{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Bonsai.Match
import Bonsai.Pattern
import STLC
import Bonsai.SyntaxSpec
import Utils.Timing

x1 :: STLCTree
x1 =
  BonsaiNode
    (mrgIf "cond" (mrgReturn (simpleNode "call")) (mrgReturn $ simpleNode "+"))
    (uBonsaiNode (mrgReturn $ simpleNode "+") (mrgReturn $ simpleNode "one"))

f1 :: UnionM (STLCTree)
f1 = genSym (1 :: Int) "a"

f2 :: UnionM (STLCTree)
f2 = genSym (2 :: Int) "b"

f3 :: UnionM (STLCTree)
f3 = genSym (3 :: Int) "c"

--f5 :: UnionM (STLCTree)
--f5 = genSym (5 :: Int) "e"
f8 :: UnionM (STLCTree)
f8 = genSym (8 :: Int) "h"

main :: IO ()
main = timeItAll "Overall" $ do
  print $ terminals stlcSyntax
  print $ matchStlcSyntax x1 "term"
  print f1
  print f2
  print f3
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ placeHolder ==> mrgLift
      ]
      #~ f1
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ stlcLiteral "+" ==> mrgReturn (1 :: Integer)
      ]
      #~ f1
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ placeHolder *= placeHolder ==> (\a _ -> mrgLift a)
      ]
      #~ f1
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ stlcLiteral "+" ==> mrgReturn (1 :: Integer)
      ]
      #~ f2
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ placeHolder *= placeHolder ==> (\a _ -> mrgLift a)
      ]
      #~ f2
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ stlcLiteral "+" *= placeHolder ==> lift
      ]
      #~ f3
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ stlcLiteral "cons" *= (stlcLiteral "one" *= stlcLiteral "nil") ==> mrgReturn (1 :: Integer)
      ]
      #~ f3
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ stlcLiteral "a" ==> mrgReturn (1 :: Integer),
        stlcLiteral "b" ==> mrgReturn (2 :: Integer)
      ]
      #~ f3
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer oneNode :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer nilNode :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer (simpleNode "cons") :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer (simpleNode "hd") :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer (simpleNode "tl") :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer (simpleNode "+") :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        (toCon $ typer (simpleNode "a") :: Maybe (Either BonsaiError (ConcSTLCTree)))
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        ( toCon $ typer (lambdaNode "a" intTy (simpleNode "a")) ::
            Maybe (Either BonsaiError (ConcSTLCTree))
        )
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        ( toCon $ typer (lambdaNode "a" intTy (simpleNode "b")) ::
            Maybe (Either BonsaiError (ConcSTLCTree))
        )
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        ( toCon $ typer (callNode (simpleNode "+") (simpleNode "one")) ::
            Maybe (Either BonsaiError (ConcSTLCTree))
        )
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        ( toCon $ typer (callNode (simpleNode "+") (simpleNode "one")) ::
            Maybe (Either BonsaiError (ConcSTLCTree))
        )
    )
  print
    ( (fmap . fmap)
        (showConcTree stlcSyntax)
        ( toCon $ typer (callNode (lambdaNode "a" intTy (simpleNode "a")) (simpleNode "one")) ::
            Maybe (Either BonsaiError (ConcSTLCTree))
        )
    )
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
  print $
    interpreter
      ( callNode
          ( callNode
              (lambdaNode "a" intTy (lambdaNode "b" intTy (simpleNode "a")))
              oneNode
          )
          (plusNode oneNode oneNode)
      )
  print $ interpreter (callNode (lambdaNode "a" intTy (lambdaNode "a" intTy (simpleNode "a"))) oneNode)
  print $
    interpreter
      ( callNode
          ( callNode
              (lambdaNode "a" intTy (lambdaNode "a" intTy (simpleNode "a")))
              oneNode
          )
          (plusNode oneNode oneNode)
      )

  let result = lift f8 >>= execStlc
  _ <- timeItAll "symeval" $ runExceptT result `deepseq` return ()
  r <- timeItAll "lower/solve" $ solveWithTranslation VerifyTyper (BoundedReasoning @6 boolector) result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree stlcSyntax <$> (toCon $ symeval True mo f8 :: Maybe (ConcSTLCTree))
