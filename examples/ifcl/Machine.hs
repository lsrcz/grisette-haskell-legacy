module Machine where

import Control.Monad.Except
import GHC.Generics
import Grisette.Core
import Grisette.Lib
import Grisette.SymPrim.Term hiding (insert)
import Instructions
import Value
import Control.Exception
import Prelude hiding (pred)
import Control.DeepSeq

data Errors = EvalError deriving (Show, Eq, Generic, Mergeable SymBool)

instance TransformError ArrayException Errors where
  transformError _ = EvalError

instance TransformError Errors Errors where
  transformError _ = EvalError

takeOnlyEnough :: (Mergeable SymBool a) => [a] -> SymInteger -> ExceptT Errors UnionM [a]
takeOnlyEnough l i =
  mrgGuard
    (i ==~ 0)
    (return [])
    ( case l of
        [] -> throwError EvalError
        x : xs -> do
          t <- takeOnlyEnough xs (i - 1)
          return $! x : t
    )

dropOnlyEnough :: (Mergeable SymBool a) => [a] -> SymInteger -> ExceptT Errors UnionM [a]
dropOnlyEnough l i =
  mrgGuard
    (i ==~ 0)
    (return l)
    ( case l of
        [] -> throwError EvalError
        _ : xs -> dropOnlyEnough xs (i - 1)
    )

replace :: (Mergeable SymBool a) => [a] -> SymInteger -> a -> ExceptT Errors UnionM [a]
replace [] _ _ = throwError EvalError
replace (x : xs) v t =
  mrgGuard
    (v ==~ 0)
    (return $! t : xs)
    ( do
        r <- replace xs (v - 1) t
        return $! x : r
    )

insert :: (Mergeable SymBool a) => [a] -> SymInteger -> a -> ExceptT Errors UnionM [a]
insert l i v =
  mrgGuard
    (i ==~ 0)
    (return $! v : l)
    ( case l of
        [] -> throwError EvalError
        (x : xs) -> do
          r <- insert xs (i - 1) v
          return $! x : r
    )

data Machine = Machine
  { pc :: PCValue,
    stack :: UnionM [UnionM MemValue],
    mem :: UnionM [UnionM PCValue]
  }
  deriving (Show, Eq, Generic, Mergeable SymBool)
  deriving (SimpleMergeable SymBool, NFData)

freshMachine :: Int -> Machine
freshMachine memCell = Machine zeroLow (mrgSingle []) (mrgSingle $ replicate memCell (mrgSingle zeroLow))

type Program = [UnionM Instruction]

data Exact = Exact [InstructionSpec]

instance SymGen SymBool Exact Program where
instance SymGenSimple SymBool Exact Program where
  genSymSimpleIndexed (Exact spec) = traverse genSymIndexed spec

loc :: Program -> Int
loc = length

isHalted :: Machine -> Program -> SymBool
isHalted m p = int (pc m) ==~ fromIntegral (loc p)

isHaltedWithLow :: Machine -> Program -> SymBool
isHaltedWithLow m p = isHalted m p &&~ nots (label (pc m))

peek :: SymInteger -> Machine -> ExceptT Errors UnionM MemValue
peek i m = do
  s <- lift $ stack m
  r <- s !!~ i
  mrgLift r

peekPC :: SymInteger -> Machine -> ExceptT Errors UnionM PCValue
peekPC i m = do
  p <- peek i m
  case p of
    MPCValue pv -> mrgReturn pv
    ReturnAddr {} -> throwError EvalError


push :: MemValue -> Machine -> Machine
push v (Machine p s m) = Machine p (mrgFmap (mrgSingle v :) s) m

pushAt :: SymInteger -> MemValue -> Machine -> ExceptT Errors UnionM Machine
pushAt i v (Machine p s m) = do
  st <- lift s
  mrgGuard (fromIntegral (length st) <~ i) (throwError EvalError) $ do
    newst <- insert st i (mrgSingle v)
    return $! Machine p (mrgSingle newst) m

pop :: Machine -> ExceptT Errors UnionM Machine
pop = popN 1

popN :: SymInteger -> Machine -> ExceptT Errors UnionM Machine
popN i (Machine p s m) = do
  st <- lift s
  mrgGuard (fromIntegral (length st) <~ i) (throwError EvalError) $ do
    newst <- dropOnlyEnough st i
    return $! Machine p (mrgSingle newst) m

-- concrete pred
popUntil :: (MemValue -> Bool) -> Machine -> ExceptT Errors UnionM Machine
popUntil pred (Machine p s m) = do
  st <- lift s
  newst <- computeStack st
  return $! Machine p (mrgSingle newst) m
  where
    computeStack :: [UnionM MemValue] -> ExceptT Errors UnionM [UnionM MemValue]
    computeStack [] = mrgReturn []
    computeStack st@(x : xs) = do
      xv <- lift x
      if pred xv then mrgReturn st else computeStack xs

read :: SymInteger -> Machine -> ExceptT Errors UnionM PCValue
read i (Machine _ _ m) = do
  m1 <- lift m
  r <- m1 !!~ i
  mrgLift r

write :: SymInteger -> PCValue -> Machine -> ExceptT Errors UnionM Machine
write i v (Machine p s m) = do
  mv <- lift m
  mrgGuard (fromIntegral (length m) <~ i) (throwError EvalError) $ do
    newMem <- replace mv i $ mrgSingle v
    return $! Machine p s (mrgSingle newMem)

goto :: PCValue -> Machine -> Machine
goto n (Machine _ s m) = Machine n s m

next :: Machine -> Machine
next (Machine (PCValue i l) s m) = Machine (PCValue (i + 1) l) s m


