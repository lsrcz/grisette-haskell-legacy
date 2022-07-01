{-# LANGUAGE TemplateHaskell #-}

module Lang where

import GHC.Generics
import Grisette
import Grisette.Unordered.UUnionM

type Ino = Integer

type Content = [Bool]

type Fd = Integer

type Name = Integer

type BlockSize = Integer

type Off = Integer

data SysCall
  = Creat Name
  | Write Fd Content
  | Rename Name Name
  | Efsync (UUnionM Fd) SymBool
  deriving (Show, Eq, Generic)
  deriving (Mergeable SymBool, Evaluate Model) via (Default SysCall)

removeDisabledSyncs :: [SysCall] -> [SysCall]
removeDisabledSyncs [] = []
removeDisabledSyncs (Efsync _ v : xs) | v == conc False = removeDisabledSyncs xs
removeDisabledSyncs (x : xs) = x : removeDisabledSyncs xs

newtype GenEfsync = GenEfsync Integer

instance GenSym SymBool GenEfsync SysCall

instance GenSymSimple SymBool GenEfsync SysCall where
  genSymSimpleFresh (GenEfsync n) = do
    fds <- choose [0 .. n -1]
    b <- genSymSimpleFresh @SymBool ()
    return $ Efsync fds b

data InodeOp
  = IDirAdd Name Fd
  | IDirRename Name Name
  | IFileWrite Fd Content Off
  | ISwap Fd Bool
  | IFileSetSize Fd Integer
  | IFileExtend Fd Content Off Integer
  deriving (Show, Eq)

instance Mergeable SymBool InodeOp where
  mergingStrategy = NoStrategy

$(makeUnionMWrapper "u" ''InodeOp)

isDirOp :: InodeOp -> Bool
isDirOp IDirAdd {} = True
isDirOp IDirRename {} = True
isDirOp _ = False

dirSameInoDeps :: InodeOp -> InodeOp -> Bool
dirSameInoDeps i1 i2 = isDirOp i1 && isDirOp i2

barrierDeps :: InodeOp -> InodeOp -> Bool
barrierDeps (ISwap _ True) _ = True
barrierDeps _ (ISwap _ True) = True
barrierDeps _ _ = False

metadataSameInoDeps :: InodeOp -> InodeOp -> Bool
metadataSameInoDeps (IFileSetSize fd1 _) (IFileSetSize fd2 _) = fd1 == fd2
metadataSameInoDeps (IFileSetSize fd1 _) (IFileExtend fd2 _ _ _) = fd1 == fd2
metadataSameInoDeps (IFileExtend fd1 _ _ _) (IFileSetSize fd2 _) = fd1 == fd2
metadataSameInoDeps (IFileExtend fd1 _ _ _) (IFileExtend fd2 _ _ _) = fd1 == fd2
metadataSameInoDeps _ _ = False

sameFileBlockDeps :: InodeOp -> InodeOp -> BlockSize -> Bool
sameFileBlockDeps i1 i2 blockSize = shouldCheck && check
  where
    -- no open calls, so same fd means same ino
    shouldCheck = case (i1, i2) of
      (IFileWrite fd1 _ _, IFileWrite fd2 _ _) -> fd1 == fd2
      (IFileWrite fd1 _ _, IFileExtend fd2 _ _ _) -> fd1 == fd2
      (IFileExtend fd1 _ _ _, IFileWrite fd2 _ _) -> fd1 == fd2
      (IFileExtend fd1 _ _ _, IFileExtend fd2 _ _ _) -> fd1 == fd2
      _ -> False
    check = op1Block == op2Block
    off i = case i of
      IFileWrite _ _ o -> o
      IFileExtend _ _ o _ -> o
      _ -> error "Bad call"
    {-
    size i = case i of
      IFileWrite _ content _ -> length content
      IFileExtend _ content _ _ -> length content
      _ -> error "Bad call"
    -}
    op1Off = off i1
    op2Off = off i2
    {-
    op1Size = size i1
    op2Size = size i2
    -}
    -- I believe that this is a bug in the original benchmark, but for apple-to-apple comparison,
    -- we left it unfixed
    op1Block = if op1Off `rem` blockSize == 0 then op1Off else op1Off - op1Off `rem` blockSize
    op2Block = if op2Off `rem` blockSize == 0 then op2Off else op2Off - op2Off `rem` blockSize

fileWriteExtendDeps :: InodeOp -> InodeOp -> Bool -> Bool
fileWriteExtendDeps (IFileWrite fd1 _ _) (IFileExtend fd2 _ _ _) _ = fd1 == fd2
fileWriteExtendDeps (IFileWrite fd1 _ _) (IFileSetSize fd2 _) True = fd1 == fd2
fileWriteExtendDeps _ _ _ = False
