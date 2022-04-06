{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.State.Strict
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

data ConcPoint = ConcPoint Integer Integer deriving (Show, Generic)
  deriving (ToCon Point) via (Default ConcPoint)

data Point = Point SymInteger SymInteger
  deriving (Show, Generic, SymGen SymBool ())
  deriving (Evaluate Model, Mergeable SymBool) via (Default Point)

instance SymGenSimple SymBool () Point where
  genSymSimpleIndexed () = do
    x <- genSymSimpleIndexed @SymBool ()
    y <- genSymSimpleIndexed @SymBool ()
    return $ Point x y

gridRef :: Point -> StateT Grid (ExceptT () UnionM) (UnionM (Maybe B.ByteString))
gridRef (Point x y) = do
  g <- get
  l1 <- g !!~ x
  l1 !!~ y

gridSet :: Point -> UnionM (Maybe B.ByteString) -> StateT Grid (ExceptT () UnionM) ()
gridSet (Point x y) v = do
  g <- get
  xlist <- g !!~ x
  r <- replaceNth y v xlist
  g1 <- replaceNth x r g
  merge $ put g1

unsafeSet :: Grid -> Int -> Int -> UnionM (Maybe B.ByteString) -> Grid
unsafeSet g x y v =
  let xlist = g !! x
      r = unsafeReplaceNth y v xlist
   in unsafeReplaceNth x r g

data Dir = N | S | W | E
  deriving (Show, Generic)
  deriving (Mergeable SymBool, Evaluate Model, ToCon Dir) via (Default Dir)

translatePoint :: Point -> Dir -> Point
translatePoint (Point x y) N = Point (x - 1) y
translatePoint (Point x y) S = Point (x + 1) y
translatePoint (Point x y) W = Point x (y - 1)
translatePoint (Point x y) E = Point x (y + 1)

instance SymGen SymBool () Dir where
  genSymIndexed () = choose N [S, W, E]

move :: Point -> Dir -> StateT Grid (ExceptT () UnionM) ()
move p d = do
  droplet <- gridRef p
  let newpoint = translatePoint p d
  gridSet p (mrgReturn Nothing)
  gridSet newpoint droplet

assert :: (MonadError () m, MonadUnion SymBool m) => SymBool -> m ()
assert = gassertWithError ()

mix :: Point -> StateT Grid (ExceptT () UnionM) ()
mix p = do
  let e = translatePoint p E
  let se = translatePoint e S
  let s = translatePoint p S
  a <- gridRef p
  b <- gridRef e
  assert #~ mrgFmap (conc . isJust) a
  assert #~ mrgFmap (conc . isJust) b
  gridSet p (uJust "c")
  gridSet e (uJust "c")
  merge $ replicateM_ 3 $ do
    move p E
    move e S
    move se W
    move s N

data ConcInstruction = ConcMove ConcPoint Dir | ConcMix ConcPoint
  deriving (Show, Generic)
  deriving (ToCon Instruction) via (Default ConcInstruction)

data Instruction = Move Point (UnionM Dir) | Mix Point
  deriving (Show, Generic)
  deriving (Mergeable SymBool, Evaluate Model) via (Default Instruction)

instance SymGen SymBool () Instruction where
  genSymIndexed _ = do
    p <- genSymSimpleIndexed @SymBool ()
    d <- genSymIndexed ()
    choose (Move p d) [Mix p]

interpretInstruction :: Instruction -> StateT Grid (ExceptT () UnionM) ()
interpretInstruction (Move p ud) = (lift . lift) ud >>= move p
interpretInstruction (Mix p) = mix p

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
              merge $ execStateT (interpretInstruction ins) t1
            cond = newst >>= f
         in do
              print num
              _ <- timeItAll "evaluate" $ runExceptT cond `deepseq` return cond
              r <- timeItAll "lower/solve" $ solveWithTranslation Synth config cond
              case r of
                Left _ -> go (num + 1) newst
                Right m -> return $ toCon $ evaluate True m $ take (num + 1) lst

initSt :: Grid
initSt = unsafeSet (unsafeSet (makeGrid 5 5) 0 0 (uJust "a")) 0 2 (uJust "b")

spec :: StateT Grid (ExceptT () UnionM) SymBool
spec = do
  r <- gridRef (Point 4 2)
  r2 <- gridRef (Point 0 0)
  return $ r ==~ uJust "a" &&~ r2 ==~ uJust "b"

main :: IO ()
main = timeItAll "Overall" $ do
  let (x :: UnionM Instruction) = genSym @SymBool () "a"
  print x
  synthr <- synthesizeProgram (UnboundedReasoning z3 {verbose = False, timing = PrintTiming}) 20 initSt (merge . evalStateT spec)
  print synthr
