{-# LANGUAGE OverloadedStrings #-}

module Main where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import qualified Data.ByteString as B
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Bonsai.Match
import NanoScala
import Bonsai.Pattern
import Bonsai.SyntaxSpec
import Utils.Timing

simpleNode :: B.ByteString -> DotTree
simpleNode = unsafeLeaf dotSyntax

pairNode :: DotTree -> DotTree -> DotTree
pairNode l r = BonsaiNode (mrgReturn l) (mrgReturn r)

valNode :: B.ByteString -> DotTree -> DotTree
valNode name term = pairNode (simpleNode "val") $ pairNode (simpleNode name) term

typNode :: B.ByteString -> DotTree -> DotTree
typNode name term = pairNode (simpleNode "typ") $ pairNode (simpleNode name) term

andNode :: DotTree -> DotTree -> DotTree
andNode l r = pairNode (simpleNode "and") $ pairNode l r

letNode :: B.ByteString -> DotTree -> DotTree -> DotTree -> DotTree -> DotTree
letNode name inty outty value expr =
  pairNode (simpleNode "let") $
    pairNode (pairNode (simpleNode name) $ pairNode inty outty) $
      pairNode value expr

varNode :: B.ByteString -> DotTree
varNode name = pairNode (simpleNode "var") $ simpleNode name

nullNode :: DotTree
nullNode = simpleNode "null"

dieNode :: DotTree -> DotTree
dieNode = pairNode $ simpleNode "die"

makeNullNode :: DotTree -> DotTree
makeNullNode = pairNode $ simpleNode "make-null"

anyNode :: DotTree
anyNode = simpleNode "Any"

nothingNode :: DotTree
nothingNode = simpleNode "Nothing"

getNode :: DotTree -> B.ByteString -> DotTree
getNode term name = pairNode (simpleNode "get") $ pairNode term (simpleNode name)

rangeNode :: B.ByteString -> DotTree -> DotTree -> DotTree
rangeNode name lower upper =
  pairNode (simpleNode "typ") $
    pairNode (simpleNode name) $ pairNode (simpleNode "range") $ pairNode lower upper

aNode :: DotTree
aNode = simpleNode "a"

bNode :: DotTree
bNode = simpleNode "b"

cNode :: DotTree
cNode = simpleNode "c"

f4 :: UnionM DotTree
f4 = genSym (4 :: Int) "a"

f10 :: UnionM DotTree
f10 = genSym (10 :: Int) "a"

counterExample :: DotTree
counterExample =
  dieNode $
    letNode
      "a"
      (typNode "b" anyNode)
      (getNode (varNode "a") "b")
      (makeNullNode (andNode (typNode "b" nothingNode) (typNode "b" anyNode)))
      nullNode

main :: IO ()
main = do
  print $ terminals dotSyntax
  print f4
  print $
    bonsaiMatchCustomError
      BonsaiTypeError
      [ dotLiteral "val" *= (placeHolder *= placeHolder) ==> \a _ -> mrgLift a
      ]
      #~ f4
  print $ typer nullNode
  print $ typer (dieNode nullNode)
  let typErrNode = rangeNode "c" anyNode nothingNode
  print typErrNode
  let failingNode = dieNode $ letNode "b" typErrNode (getNode (varNode "b") "c") (makeNullNode typErrNode) nullNode
  print $ typer failingNode
  print $ eval failingNode

  let qnode = letNode "b" nothingNode nothingNode nullNode (dieNode $ varNode "b")
  print $ typer qnode
  print $ eval qnode

  let result = lift f10 >>= execDot
  _ <- timeItAll "symeval" $ runExceptT result `deepseq` return ()
  r <- timeItAll "lower/solve" $ solveWithTranslation VerifyTyper (BoundedReasoning @6 boolector) result
  case r of
    Left _ -> putStrLn "Verified"
    Right mo -> do
      putStrLn "Found bad"
      print $ showConcTree dotSyntax <$> (toCon $ symeval True mo f10 :: Maybe ConcDotTree)
