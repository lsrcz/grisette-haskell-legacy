module Interpret where

import Control.Monad.State.Strict
import Fs
import Grisette
import Lang

interpretOps :: (FileSystem conc fs, Mergeable SymBool fs) => [UnionM InodeOp] -> fs -> UnionM fs
interpretOps [] fs = mrgReturn fs
interpretOps (x : xs) fs = do
  i <- x
  r <- execute fs i
  interpretOps xs r

interpretConc :: forall conc fs. (FileSystem conc fs, Mergeable SymBool fs) => [SysCall] -> conc -> Maybe conc
interpretConc s fs =
  ( case interpretOps (crack fs s) (toSym fs) :: UnionM fs of
      SingleU x -> Just x
      _ -> Nothing
  )
    >>= toCon

zoomy :: GenSymFresh a -> StateT [SymBool] GenSymFresh a
zoomy f = StateT $ \s -> (,s) <$> f {-do
                                    (inner, l) <- get
                                    (a, newInner) <- lift $ runStateT s inner
                                    put (newInner, l)
                                    return a-}

nonDet :: StateT [SymBool] GenSymFresh SymBool
nonDet = do
  v <- zoomy (genSymSimpleFresh ())
  modify $ (v :)
  return v

interpretOrderOps ::
  forall conc fs.
  (FileSystem conc fs, Mergeable SymBool fs, Show fs) =>
  [UnionM InodeOp] ->
  [UnionM Integer] ->
  UnionM fs ->
  StateT [SymBool] GenSymFresh (UnionM fs)
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
       in go1 x ls
            &&~ ( (x >~ l)
                    `implies` ( ((\xv lv -> conc (reorder fs xv lv)) #~ opx #~ opl)
                                  &&~ (\xv lv -> conc (reorder fs xv lv))
                                  #~ opl
                                  #~ opx
                              )
                )

validOrdering :: forall conc fs. (FileSystem conc fs) => conc -> [UnionM InodeOp] -> [UnionM Integer] -> SymBool
validOrdering fs iops ordering = isPermutation ordering &&~ reorderOk fs iops ordering

insertSynthSyncs :: Integer -> [SysCall] -> GenSymFresh [SysCall]
insertSynthSyncs i [] = do
  e <- genSymSimpleFresh (GenEfsync i)
  return [e]
insertSynthSyncs i (x : xs) = do
  e <- genSymSimpleFresh (GenEfsync i)
  tl <- insertSynthSyncs i xs
  return $ e : x : tl
