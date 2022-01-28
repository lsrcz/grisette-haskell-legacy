{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveAnyClass #-}

module Main where

import Control.Monad.Except
import qualified Data.ByteString as B
import GHC.Generics
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymGen
import Grisette.Data.Functor
import Grisette.Data.List
import Grisette.Data.SymPrim
import Data.Maybe (isJust)
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Prim.Model
import Data.SBV hiding (Mergeable)
import Utils.Timing

type Grid = [[UnionM (Maybe B.ByteString)]]

makeGrid :: Integer -> Integer -> Grid
makeGrid height width = [[mrgReturn Nothing | _ <- [0 .. width - 1]] | _ <- [0 .. height - 1]]

unsafeReplaceNth :: Int -> a -> [a] -> [a]
unsafeReplaceNth = go
  where
    go _ _ [] = error "Failed"
    go p v (x : xs) = if p == 0 then v : xs else x : go (p - 1) v xs

replaceNth :: (Mergeable SymBool a) => Sym Integer -> a -> [a] -> ExceptT () UnionM [a]
replaceNth pos val ls = go pos val ls 0
  where
    go _ _ [] _ = throwError ()
    go p v (x : xs) i = mrgGuard (p ==~ i) (mrgSingle (v : xs)) (mrgFmap (x :) $ go p v xs (i + 1))

data ConcPoint = ConcPoint Integer Integer
  deriving (Show, Generic, ToCon Point)
data Point = Point SymInteger SymInteger
  deriving (Show, Generic, SymEval Model, Mergeable SymBool)
instance SymGen SymBool () Point where
  genSymIndexed = fmap mrgSingle . genSymSimpleIndexed @SymBool
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
unsafeSet g x y v = let
  xlist = g !! x
  r = unsafeReplaceNth y v xlist
  in unsafeReplaceNth x r g

data Dir = N | S | W | E deriving (Show, Generic, Mergeable SymBool, SymEval Model, ToCon Dir)

dirx :: Dir -> SymInteger
dirx N = -1
dirx S = 1
dirx _ = 0

diry :: Dir -> SymInteger
diry W = -1
diry E = 1
diry _ = 0

translatePoint :: Point -> Dir -> Point
translatePoint (Point x y) d = Point (x + dirx d) (y + diry d)

instance SymGen SymBool () Dir where
  genSymIndexed () = choose N [S, W, E]

move :: Grid -> Point -> Dir -> ExceptT () UnionM Grid
move g p d = do
  droplet <- gridRef g p
  let newpoint = translatePoint p d
  g1 <- gridSet g p (mrgSingle Nothing)
  gridSet g1 newpoint droplet

assert :: SymBool -> ExceptT () UnionM ()
assert = gassertWithError ()

assertU :: UnionM SymBool -> ExceptT () UnionM ()
assertU = assert . getSingle . merge

performN :: (Monad m) => (a -> m a) -> Int -> a -> m a
performN f 0 a = f a
performN f x a = f a >>= performN f (x - 1)

mix :: Grid -> Point -> ExceptT () UnionM Grid
mix g p = do
  let
    e = translatePoint p E
    se = translatePoint e S
    s = translatePoint p S
   in do
     a <- gridRef g p
     b <- gridRef g e
     assertU $ mrgFmap (conc . isJust) a
     assertU $ mrgFmap (conc . isJust) b
     g1 <- gridSet g p (mrgSingle $ Just "c")
     g2 <- gridSet g1 e (mrgSingle $ Just "c")
     performN (\gx -> do
       gx1 <- move gx p E
       gx2 <- move gx1 e S
       gx3 <- move gx2 se W
       move gx3 s N
       ) 3 g2

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

synthesizeProgram :: GrisetteSMTConfig n -> Int -> Grid ->
  (Grid -> ExceptT () UnionM SymBool) -> IO (Maybe [ConcInstruction])
synthesizeProgram config i initst f = go 0 (mrgReturn initst)
  where
    lst :: [UnionM Instruction]
    lst = genSymSimple @SymBool (SimpleListSpec (toInteger i) ()) "a"
    go :: Int -> ExceptT () UnionM Grid -> IO (Maybe [ConcInstruction])
    go num st = if num == i then return Nothing else
      let
        newst = do
          t1 <- st
          ins <- lift (lst !! num)
          interpretInstruction t1 ins
        cond = getSingle $ mrgFmap (\case Left _ -> conc False; Right v -> v) $ runExceptT $ newst >>= f
       in
         do
           print num
           r <- timeItAll $ solveWith config cond
           case r of
             Left _ ->
                go (num + 1) newst
             Right m -> return $ toCon $ symeval True m $ take (num + 1) lst

initSt :: Grid
initSt = unsafeSet (unsafeSet (makeGrid 5 5) 0 0 (mrgSingle $ Just "a")) 0 2 (mrgSingle $ Just "b")

spec :: Grid -> ExceptT () UnionM SymBool
spec g = do
  r <- gridRef g (Point 4 2)
  r2 <- gridRef g (Point 0 0)
  return $ r ==~ mrgSingle (Just "a") &&~ r2 ==~ mrgSingle (Just "b")

main :: IO ()
main = timeItAll $ do
  let x = genSym @SymBool @() @Instruction () "a"
  -- let y = genSym @SymBool @() @Instruction () "b"
  print x
  {-print $ do
    g <- (lift x) >>= interpretInstruction initSt
    (lift y) >>= interpretInstruction g-}
  synthr <- synthesizeProgram (UnboundedReasoning z3 {verbose=False, timing=PrintTiming}) 20 initSt spec
  print synthr

