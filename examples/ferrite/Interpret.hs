module Interpret where

import Control.Monad.State.Strict
import Data.Bifunctor
import Fs
import Grisette.Core
import Grisette.SymPrim.Term
import Lang


interpretOps :: (FileSystem conc fs, Mergeable SymBool fs) => [UnionM InodeOp] -> fs -> UnionM fs
interpretOps [] fs = mrgReturn fs
interpretOps (x : xs) fs = do
  i <- x
  r <- execute fs i
  interpretOps xs r

interpretConc :: forall conc fs. (FileSystem conc fs, Mergeable SymBool fs) => [SysCall] -> conc -> Maybe conc
interpretConc s fs =
  toCon (interpretOps (crack fs s) (toSym fs) :: UnionM fs)

zoomy :: State SymGenState a -> State (SymGenState, [SymBool]) a
zoomy s = do
  (inner, l) <- get
  (a, newInner) <- lift $ runStateT s inner
  put (newInner, l)
  return a

nonDet :: State (SymGenState, [SymBool]) SymBool
nonDet = do
  v <- zoomy (genSymSimpleIndexed @SymBool ())
  modify $ second (v :)
  return v

interpretOrderOps ::
  forall conc fs.
  (FileSystem conc fs, Mergeable SymBool fs, Show fs) =>
  [UnionM InodeOp] ->
  [UnionM Integer] ->
  UnionM fs ->
  State (SymGenState, [SymBool]) (UnionM fs)
interpretOrderOps _ [] fs = return fs
interpretOrderOps l (x : xs) fs = do
  let fs1 = do
        f <- fs
        x1 <- x
        i <- l !! fromInteger x1
        merge $ execute f i
  r <- interpretOrderOps l xs fs1
  cond <- nonDet
  return $ mrgIf cond fs r

isPermutation :: [UnionM Integer] -> SymBool
isPermutation l = go [0 .. fromIntegral (length l) - 1]
  where
    go [] = conc True
    go (x : xs) = go1 x l ==~ 1 &&~ go xs
    go1 :: Integer -> [UnionM Integer] -> SymInteger
    go1 _ [] = 0
    go1 n (x : xs) = ites @SymBool (x ==~ mrgReturn n) 1 0 + go1 n xs

reorderOk :: forall conc fs. (FileSystem conc fs) => conc -> [UnionM InodeOp] -> [UnionM Integer] -> SymBool
reorderOk fs iops = go
  where
    go [] = conc True
    go (x : xs) = go1 x xs &&~ go xs
    go1 _ [] = conc True
    go1 x (l : ls) =
      let opx = (\v -> iops !! fromInteger v) =<< x
          opl = (\v -> iops !! fromInteger v) =<< l
       in
         go1 x ls
            &&~ ((x >~ l) `implies` (((\xv lv -> conc (reorder fs xv lv)) #~ opx #~ opl) &&~
            (\xv lv -> conc (reorder fs xv lv)) #~ opl #~ opx))

validOrdering :: forall conc fs. (FileSystem conc fs) => conc -> [UnionM InodeOp] -> [UnionM Integer] -> SymBool
validOrdering fs iops ordering = isPermutation ordering &&~ reorderOk fs iops ordering

insertSynthSyncs :: Integer -> [SysCall] -> State SymGenState [SysCall]
insertSynthSyncs i [] = do
  e <- genSymSimpleIndexed @SymBool (GenEfsync i)
  return [e]
insertSynthSyncs i (x : xs) = do
  e <- genSymSimpleIndexed @SymBool (GenEfsync i)
  tl <- insertSynthSyncs i xs
  return $ e : x : tl
