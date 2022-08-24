module Ext4 where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.HashMap.Strict as M
import Data.Maybe
import Fs
import GHC.Generics
import Grisette
import Lang

data ConcDirEnt = ConcDirEnt {concDirEntIno :: Integer, concDirEntExists :: Bool}
  deriving (Show, Eq, Generic)
  deriving (ToCon DirEnt) via (Default ConcDirEnt)

data DirEnt = DirEnt {dirEntIno :: UnionM Integer, dirEntExists :: SymBool}
  deriving (Show, Eq, Generic)
  deriving (Mergeable SymBool, ToSym ConcDirEnt, SimpleMergeable SymBool, Evaluate Model) via (Default DirEnt)

data ConcFile = ConcFile {concFileSize :: Integer, concFileOnDisk :: [Bool]}
  deriving (Show, Eq, Generic)
  deriving (ToCon File) via (Default ConcFile)

data File = File {fileSize :: UnionM Integer, fileOnDisk :: UnionM [SymBool]}
  deriving (Show, Eq, Generic)
  deriving (Mergeable SymBool, ToSym ConcFile, SimpleMergeable SymBool, Evaluate Model) via (Default File)

data ConcExt4Fs = ConcExt4Fs
  { concExt4BlockSize :: Integer,
    concExt4NodeAlloc :: Bool,
    concExt4Dir :: [ConcDirEnt],
    concExt4Fds :: [Integer],
    concExt4Files :: [ConcFile]
  }
  deriving (Show, Eq, Generic)
  deriving (ToCon Ext4Fs) via (Default ConcExt4Fs)

data Ext4Fs = Ext4Fs
  { ext4BlockSize :: Integer,
    ext4NodeAlloc :: Bool,
    ext4Dir :: [DirEnt],
    ext4Fds :: [UnionM Integer],
    ext4Files :: [File]
  }
  deriving (Show, Eq, Generic)
  deriving (ToSym ConcExt4Fs, Evaluate Model) via (Default Ext4Fs)

instance Mergeable SymBool Ext4Fs where
  mergingStrategy = SimpleStrategy $ \cond (Ext4Fs bs1 na1 dir1 fds1 files1) (Ext4Fs _ _ dir2 fds2 files2) ->
    -- assume bs1 == bs2
    -- assume na1 == na2
    -- assume length dir1 == length dir2
    -- assume length fds1 == length fds2
    -- assume length files1 == length files2
    Ext4Fs
      bs1
      na1
      (zipWith (mrgIte cond) dir1 dir2)
      (zipWith (mrgIte cond) fds1 fds2)
      (zipWith (mrgIte cond) files1 files2)

ext4fs :: Integer -> Integer -> Bool -> ConcExt4Fs
ext4fs capacity blockSize nodealloc =
  ConcExt4Fs
    blockSize
    nodealloc
    [ConcDirEnt n False | n <- [0 .. (capacity - 1)]]
    [0 | _ <- [0 .. (capacity - 1)]]
    [ConcFile 0 [] | _ <- [0 .. (capacity - 1)]]

roundUp :: Integer -> BlockSize -> Integer
roundUp x blockSize = if x `rem` blockSize == 0 then x else x + blockSize - x `rem` blockSize

data Ext4FsCrackState = Ext4FsCrackState
  { ext4NextFd :: Fd,
    lengths :: M.HashMap Fd Integer,
    blockLengths :: M.HashMap Fd Integer
  }
  deriving (Show, Eq) -- , Generic, Mergeable SymBool)

-- $(makeUnionMWrapper "u" ''Ext4FsCrackState)

updateNextFd :: State Ext4FsCrackState ()
updateNextFd = modify $ \(Ext4FsCrackState n l b) -> Ext4FsCrackState (n + 1) l b

updateLength :: Fd -> Integer -> State Ext4FsCrackState ()
updateLength fd len = modify $ \(Ext4FsCrackState n l b) -> Ext4FsCrackState n (M.insert fd len l) b

getLength :: Fd -> State Ext4FsCrackState Integer
getLength fd = gets $ \s -> fromJust $ M.lookup fd (lengths s)

updateBlockLength :: Fd -> Integer -> State Ext4FsCrackState ()
updateBlockLength fd len = modify $ \(Ext4FsCrackState n l b) -> Ext4FsCrackState n l (M.insert fd len b)

getBlockLength :: Fd -> State Ext4FsCrackState Integer
getBlockLength fd = gets $ \s -> fromJust $ M.lookup fd (blockLengths s)

getNameIno :: Name -> StateT Ext4Fs UnionM (UnionM Integer)
getNameIno nm = merge $ gets $ \(Ext4Fs _ _ dir _ _) -> dirEntIno $ dir !! fromInteger nm

getFdINode :: Fd -> StateT Ext4Fs UnionM (UnionM Integer)
getFdINode fd = merge $ gets $ \(Ext4Fs _ _ _ fds _) -> fds !! fromInteger fd

getFile :: UnionM Ino -> StateT Ext4Fs UnionM File
getFile ino = StateT $ \s -> do
  i <- ino
  mrgReturn (ext4Files s !! fromInteger i, s)

getDirEnt :: Name -> StateT Ext4Fs UnionM DirEnt
getDirEnt nm = merge $ gets $ \(Ext4Fs _ _ dir _ _) -> dir !! fromInteger nm

updateL :: Int -> a -> [a] -> [a]
updateL 0 x (_ : ys) = x : ys
updateL n x (y : ys) = y : updateL (n - 1) x ys
updateL _ _ _ = error "Bad"

updateFile :: UnionM Ino -> File -> StateT Ext4Fs UnionM ()
updateFile ino f = StateT $ \(Ext4Fs bs na dir fd files) -> do
  i <- ino
  mrgReturn ((), Ext4Fs bs na dir fd $ updateL (fromIntegral i) f files)

updateDirEnt :: Name -> DirEnt -> StateT Ext4Fs UnionM ()
updateDirEnt nm d = merge $
  modify $ \(Ext4Fs bs na dir fd files) ->
    Ext4Fs bs na (updateL (fromInteger nm) d dir) fd files

updateFdIno :: Fd -> UnionM Ino -> StateT Ext4Fs UnionM ()
updateFdIno fd ino = merge $
  modify $ \(Ext4Fs bs na dir fds files) ->
    Ext4Fs bs na dir (updateL (fromInteger fd) ino fds) files

instance FileSystem ConcExt4Fs Ext4Fs where
  crack (ConcExt4Fs blockSize _ dir fds files) syscalls = evalState (go syscalls) initialState
    where
      fdFiles = fmap ((files !!) . fromIntegral) fds
      initialState =
        Ext4FsCrackState
          0
          (M.fromList [(fd, concFileSize file) | (fd, file) <- zip [0 ..] fdFiles])
          ( M.fromList
              [ (fd, fromIntegral $ length $ concFileOnDisk file)
                | (fd, file) <- zip [0 ..] fdFiles
              ]
          )
      go [] = return []
      go (Creat nm : xs) = do
        nextFd <- gets ext4NextFd
        let ino = concDirEntIno (dir !! fromIntegral nm)
        let cnt = concFileOnDisk (files !! fromIntegral ino)
        r <- go xs
        updateLength nextFd $ fromIntegral $ length cnt
        updateNextFd
        return $! uIDirAdd nm nextFd : r
      go (Write fd content : xs) = do
        offset <- getLength fd
        let offsetEnd = offset + fromIntegral (length content)
        ops <- fill offset
        r <- res offset (roundUp offset blockSize) offsetEnd
        r2 <- go xs
        return $! ops ++ r ++ r2
        where
          fill off =
            if off == roundUp off blockSize
              then return []
              else do
                len <- getLength fd
                updateLength fd (len + fromIntegral (length chunk))
                return [uIFileWrite fd chunk off, uIFileSetSize fd (off + fromIntegral (length chunk))]
            where
              chunk :: [Bool]
              chunk = take (min (length content) (fromIntegral $ roundUp off blockSize - off)) content
          res offset pos offsetEnd =
            if pos >= offsetEnd
              then return []
              else do
                let posEnd = pos + blockSize
                let chunk =
                      drop (fromIntegral $ pos - offset) $
                        take (min (length content) (fromIntegral $ posEnd - offset)) content
                len <- getLength fd
                updateLength fd (len + fromIntegral (length chunk))
                blen <- getBlockLength fd

                if posEnd <= blen
                  then return [uIFileWrite fd chunk pos, uIFileSetSize fd posEnd]
                  else do
                    ts1 <-
                      ( if length chunk <= fromIntegral blockSize
                          then
                            return
                              [ uIFileExtend
                                  fd
                                  (chunk ++ replicate (fromIntegral blockSize - length chunk) False)
                                  pos
                                  offsetEnd
                              ]
                          else return [uIFileExtend fd chunk pos offsetEnd]
                        )
                    updateBlockLength fd posEnd
                    return ts1
      go (Rename name1 name2 : xs) = do
        r <- go xs
        return $ uIDirRename name1 name2 : r
      go (Efsync fd e : xs) = do
        r <- go xs
        return $ (fd >>= (\fdv -> mrgIf e (uISwap fdv True) (uISwap fdv False))) : r
  execute f i =
    execStateT
      ( case i of
          IDirAdd nm fd -> do
            DirEnt ino _ <- getDirEnt nm
            updateDirEnt nm $ DirEnt ino (conc True)
            updateFdIno fd ino
          IDirRename name1 name2 -> unless (name1 == name2) $ do
            newIno <- getNameIno name1
            oldIno <- getNameIno name2
            updateFile oldIno (File 0 (mrgReturn []))
            updateDirEnt name1 $ DirEnt oldIno (conc False)
            updateDirEnt name2 $ DirEnt newIno (conc True)
          IFileWrite fd content off -> doWrite fd content off
          ISwap _ _ -> mrgReturn @SymBool ()
          IFileSetSize fd sz -> updateSize fd sz
          IFileExtend fd content off sz -> do
            doWrite fd content off
            updateSize fd sz
      )
      f
    where
      doWrite fd content off = do
        ino <- getFdINode fd
        File sz onDisk <- getFile ino
        let offEnd = off + fromIntegral (length content)
        let onDiskUpdated = do
              o <- onDisk
              if fromIntegral off > length o
                then mrgReturn $ o ++ replicate (fromIntegral off - length o) (conc False)
                else mrgReturn o
        let headAndTail = do
              o <- onDiskUpdated
              let hd = take (fromIntegral off) o
              let tl = if fromIntegral offEnd < length o then drop (fromIntegral offEnd) o else []
              mrgReturn (hd, tl)
        let newContent = do
              (hd, tl) <- headAndTail
              mrgReturn $ hd ++ toSym content ++ tl
        let newFile = File sz newContent
        updateFile ino newFile
      updateSize fd sz = do
        ino <- getFdINode fd
        File _ onDisk <- getFile ino
        let newFile = File (mrgReturn sz) onDisk
        updateFile ino newFile
  ondisk (Ext4Fs _ _ dirs _ files) nm =
    let DirEnt ino exists = dirs !! fromIntegral nm
     in mrgIf
          exists
          ( do
              i <- ino
              let File sz od = files !! fromIntegral i
              s <- sz
              ods <- od
              uJust $ take (fromIntegral s) ods
          )
          uNothing
  reorder (ConcExt4Fs bs na _ _ _) call1 call2 =
    not (dirSameInoDeps call1 call2)
      && not (barrierDeps call1 call2)
      && not (metadataSameInoDeps call1 call2)
      && not (sameFileBlockDeps call1 call2 bs)
      && not (fileWriteExtendDeps call1 call2 na)
