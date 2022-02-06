{-# LANGUAGE OverloadedStrings #-}

module NanoScalaMain where

import BonsaiTree
import qualified Data.ByteString as B
import Grisette.Core
import NanoScala
import SyntaxSpec
import Error
import Grisette.SymPrim.Term
import Control.Monad.Trans
import Utils.Timing
import Control.DeepSeq
import Grisette.Backend.SBV
import Control.Monad.Except

simpleNode :: B.ByteString -> DotTree
simpleNode = unsafeLeaf dotSyntax

pairNode :: DotTree -> DotTree -> DotTree
pairNode l r = BonsaiNode (mrgSingle l) (mrgSingle r)

valNode :: B.ByteString -> DotTree -> DotTree
valNode name term = pairNode (simpleNode "val") $ pairNode (simpleNode name) term

typNode :: B.ByteString -> DotTree -> DotTree
typNode name term = pairNode (simpleNode "typ") $ pairNode (simpleNode name) term

andNode :: DotTree -> DotTree -> DotTree
andNode l r = pairNode (simpleNode "and") $ pairNode l r

letNode ::
  B.ByteString ->
  DotTree ->
  DotTree ->
  DotTree ->
  DotTree ->
  DotTree
letNode name inty outty value expr =
  pairNode
    (simpleNode "let")
    $ pairNode
      (pairNode (simpleNode name) $ pairNode inty outty)
      $ pairNode value expr

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

f10 :: UnionM DotTree
f10 = genSym (10 :: Int) "a"

counterExample :: DotTree
counterExample = dieNode $
  letNode "a" (typNode "b" anyNode) (getNode (varNode "a") "b")
    (makeNullNode (andNode (typNode "b" nothingNode) (typNode "b" anyNode)))
    nullNode

dotMain :: IO ()
dotMain = do
  print $ terminals dotSyntax
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