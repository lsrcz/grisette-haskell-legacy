{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.DeepSeq
import Control.Monad.Except
import qualified Data.ByteString as B
import Data.Maybe (isJust)
import GHC.Generics
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.Lib
import Grisette.SymPrim.Term
import Utils.Timing

type Grid = [[UnionM (Maybe B.ByteString)]]

makeGrid :: Integer -> Integer -> Grid
makeGrid height width = [[mrgReturn Nothing | _ <- [0 .. width - 1]] | _ <- [0 .. height - 1]]

unsafeReplaceNth :: Int -> a -> [a] -> [a]
unsafeReplaceNth _ _ [] = error "Failed"
unsafeReplaceNth p v (x : xs) = if p == 0 then v : xs else x : unsafeReplaceNth (p - 1) v xs

replaceNth :: (Mergeable SymBool a, MonadUnion SymBool m, MonadError () m) => Sym Integer -> a -> [a] -> m [a]
replaceNth pos val ls = go ls 0
  where
    go [] i = mrgIf (pos >=~ i :: SymBool) (throwError ()) (return [])
    go (x : xs) i = do
      hd <- mrgIf (pos ==~ i :: SymBool) (mrgReturn val) (mrgReturn x)
      tl <- go xs (i + 1)
      mrgReturn (hd : tl)

data ConcPoint = ConcPoint Integer Integer
  deriving (Show, Generic, ToCon Point)

data Point = Point SymInteger SymInteger
  deriving (Show, Generic, SymEval Model, Mergeable SymBool)

instance SymGen SymBool () Point

instance SymGenSimple SymBool () Point where
  genSymSimpleIndexed () = do
    x <- genSymSimpleIndexed @SymBool ()
    y <- genSymSimpleIndexed @SymBool ()
    return $ Point x y

gridRef :: Grid -> Point -> ExceptT () UnionM (UnionM (Maybe B.ByteString))
gridRef g (Point x y) = do
  l1 <- g !!~ x
  l1 !!~ y

gridSet :: Grid -> Point -> UnionM (Maybe B.ByteString) -> ExceptT () UnionM Grid
gridSet g (Point x y) v = do
  xlist <- g !!~ x
  r <- replaceNth y v xlist
  replaceNth x r g

unsafeSet :: Grid -> Int -> Int -> UnionM (Maybe B.ByteString) -> Grid
unsafeSet g x y v =
  let xlist = g !! x
      r = unsafeReplaceNth y v xlist
   in unsafeReplaceNth x r g

data Dir = N | S | W | E deriving (Show, Generic, Mergeable SymBool, SymEval Model, ToCon Dir)

translatePoint :: Point -> Dir -> Point
translatePoint (Point x y) N = Point (x - 1) y
translatePoint (Point x y) S = Point (x + 1) y
translatePoint (Point x y) W = Point x (y - 1)
translatePoint (Point x y) E = Point x (y + 1)

instance SymGen SymBool () Dir where
  genSymIndexed () = choose N [S, W, E]

move :: Grid -> Point -> Dir -> ExceptT () UnionM Grid
move g p d = do
  droplet <- gridRef g p
  let newpoint = translatePoint p d
  g1 <- gridSet g p (mrgReturn Nothing)
  gridSet g1 newpoint droplet

assert :: SymBool -> ExceptT () UnionM ()
assert = gassertWithError ()

performN :: (Monad m) => (a -> m a) -> Int -> a -> m a
performN f 0 a = f a
performN f x a = f a >>= performN f (x - 1)

mix :: Grid -> Point -> ExceptT () UnionM Grid
mix g p = do
  let e = translatePoint p E
      se = translatePoint e S
      s = translatePoint p S
   in do
        a <- gridRef g p
        b <- gridRef g e
        assert #~ mrgFmap (conc . isJust) a
        assert #~ mrgFmap (conc . isJust) b
        g1 <- gridSet g p (uJust "c")
        g2 <- gridSet g1 e (uJust "c")
        performN
          ( \gx -> do
              gx1 <- move gx p E
              gx2 <- move gx1 e S
              gx3 <- move gx2 se W
              move gx3 s N
          )
          2
          g2

data ConcInstruction = ConcMove ConcPoint Dir | ConcMix ConcPoint
  deriving (Show, Generic, ToCon Instruction)

data Instruction = Move Point (UnionM Dir) | Mix Point
  deriving (Show, Generic, Mergeable SymBool, SymEval Model)

instance SymGen SymBool () Instruction where
  genSymIndexed _ = do
    p <- genSymSimpleIndexed @SymBool ()
    d <- genSymIndexed ()
    choose (Move p d) [Mix p]

interpretInstruction :: Grid -> Instruction -> ExceptT () UnionM Grid
interpretInstruction g (Move p ud) = lift ud >>= move g p
interpretInstruction g (Mix p) = mix g p

data Synth = Synth

instance SolverTranslation Synth () SymBool where
  errorTranslation _ _ = False
  valueTranslation _ v = v

synthesizeProgram ::
  GrisetteSMTConfig n ->
  Int ->
  Grid ->
  (Grid -> ExceptT () UnionM SymBool) ->
  IO (Maybe [ConcInstruction])
synthesizeProgram config i initst f = go 0 (mrgReturn initst)
  where
    lst = genSymSimple @SymBool (SimpleListSpec (toInteger i) ()) "a"
    go num st
      | num == i = return Nothing
      | otherwise =
        let newst = do
              t1 <- st
              ins <- lift (lst !! num)
              interpretInstruction t1 ins
            cond = newst >>= f
         in do
              print num
              --print cond
              _ <- timeItAll "symeval" $ runExceptT cond `deepseq` return cond
              r <- timeItAll "lower/solve" $ solveWithTranslation Synth config cond
              case r of
                Left _ -> go (num + 1) newst
                Right m -> return $ toCon $ symeval True m $ take (num + 1) lst

initSt :: Grid
initSt = unsafeSet (unsafeSet (makeGrid 5 5) 0 0 (uJust "a")) 0 2 (uJust "b")

spec :: Grid -> ExceptT () UnionM SymBool
spec g = do
  r <- gridRef g (Point 4 2)
  r2 <- gridRef g (Point 0 0)
  return $ r ==~ uJust "a" &&~ r2 ==~ uJust "b"

main :: IO ()
main = timeItAll "Overall" $ do
  let x = genSym @SymBool @() @Instruction () "a"
  print x
  synthr <- synthesizeProgram (UnboundedReasoning z3 {verbose = False, timing = PrintTiming}) 20 initSt spec
  print synthr
