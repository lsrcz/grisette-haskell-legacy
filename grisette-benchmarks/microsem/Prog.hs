module Prog where

import Control.Monad.State
import GHC.Generics
import SymBool
import Test.QuickCheck.Gen

data ProgNoCond a
  = TerminalNoCond a
  | IfNoCond (ProgNoCond a) (ProgNoCond a)
  deriving (Show, Eq, Generic)

data Prog a
  = Terminal a
  | If SymBool (Prog a) (Prog a)
  deriving (Show, Eq, Generic)

genCond :: ProgNoCond a -> Prog a
genCond p = evalState (genCond' p) (0 :: Int)
  where
    nextSymBool :: State Int SymBool
    nextSymBool = do
      v <- get
      put $ v + 1
      return $ Sym $ "c" ++ show v
    genCond' :: ProgNoCond a -> State Int (Prog a)
    genCond' (TerminalNoCond v) = return $ Terminal v
    genCond' (IfNoCond l r) = do
      s <- nextSymBool
      gl <- genCond' l
      gr <- genCond' r
      return $ If s gl gr

genProg :: Int -> Int -> Gen a -> Gen (ProgNoCond a)
genProg f1 f2 gen = sized $ \n ->
  if n == 0
    then TerminalNoCond <$> gen
    else
      frequency
        [ ( f1,
            do
              l <- resize (n - 1) $ genProg f1 f2 gen
              r <- resize (n - 1) $ genProg f1 f2 gen
              return $ IfNoCond l r
          ),
          (f2, TerminalNoCond <$> gen)
        ]

genProgBad :: Int -> Int -> Gen (ProgNoCond Int)
genProgBad f1 f2 = sized $ \n ->
  if n == 0
    then TerminalNoCond <$> choose (n - 10, n)
    else
      frequency
        [ ( f1,
            do
              l <- resize (n - 1) $ genProgBad f1 f2
              r <- resize (n - 1) $ genProgBad f1 f2
              return $ IfNoCond l r
          ),
          (f2, TerminalNoCond <$> choose (n - 10, n))
        ]
