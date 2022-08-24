module Machine where

import Control.DeepSeq
import Control.Exception
import Control.Monad.Except
import GHC.Generics
import Grisette hiding (insert)
import Instructions
import Value
import Prelude hiding (pred)

data Errors = EvalError
  deriving (Show, Eq, Generic)
  deriving (Mergeable SymBool) via (Default Errors)

instance TransformError ArrayException Errors where
  transformError _ = EvalError

instance TransformError Errors Errors where
  transformError _ = EvalError

takeOnlyEnough :: (Mergeable SymBool a) => [a] -> SymInteger -> CBMCExceptT Errors UnionM [a]
takeOnlyEnough l i =
  mrgIf
    (i ==~ 0)
    (return [])
    ( case l of
        [] -> throwError EvalError
        x : xs -> do
          t <- takeOnlyEnough xs (i - 1)
          return $! x : t
    )

dropOnlyEnough :: (Mergeable SymBool a) => [a] -> SymInteger -> CBMCExceptT Errors UnionM [a]
dropOnlyEnough l i =
  mrgIf
    (i ==~ 0)
    (return l)
    ( case l of
        [] -> throwError EvalError
        _ : xs -> dropOnlyEnough xs (i - 1)
    )

replace :: (Mergeable SymBool a) => [a] -> SymInteger -> a -> CBMCExceptT Errors UnionM [a]
replace [] _ _ = throwError EvalError
replace (x : xs) v t =
  mrgIf
    (v ==~ 0)
    (return $! t : xs)
    ( do
        r <- replace xs (v - 1) t
        return $! x : r
    )

insert :: (Mergeable SymBool a) => [a] -> SymInteger -> a -> CBMCExceptT Errors UnionM [a]
insert l i v =
  mrgIf
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
  deriving (Show, Eq, Generic, NFData)
  deriving (SimpleMergeable SymBool, Mergeable SymBool) via (Default Machine)

freshMachine :: Int -> Machine
freshMachine memCell = Machine zeroLow (mrgReturn []) (mrgReturn $ replicate memCell (mrgReturn zeroLow))

type Program = [UnionM Instruction]

newtype Exact = Exact [InstructionSpec]

instance GenSym SymBool Exact Program

instance GenSymSimple Exact Program where
  genSymSimpleFresh (Exact spec) = traverse genSymFresh spec

loc :: Program -> Int
loc = length

isHalted :: Machine -> Program -> SymBool
isHalted m p = int (pc m) ==~ fromIntegral (loc p)

isHaltedWithLow :: Machine -> Program -> SymBool
isHaltedWithLow m p = isHalted m p &&~ nots (label (pc m))

peek :: SymInteger -> Machine -> CBMCExceptT Errors UnionM MemValue
peek i m = do
  s <- lift $ stack m
  r <- s !!~ i
  mrgLift r

peekPC :: SymInteger -> Machine -> CBMCExceptT Errors UnionM PCValue
peekPC i m = do
  p <- peek i m
  case p of
    MPCValue pv -> mrgReturn pv
    ReturnAddr {} -> throwError EvalError

push :: MemValue -> Machine -> Machine
push v (Machine p s m) = Machine p (mrgFmap (mrgReturn v :) s) m

pushAt :: SymInteger -> MemValue -> Machine -> CBMCExceptT Errors UnionM Machine
pushAt i v (Machine p s m) = do
  st <- lift s
  mrgIf (fromIntegral (length st) <~ i) (throwError EvalError) $ do
    newst <- insert st i (mrgReturn v)
    return $! Machine p (mrgReturn newst) m

pop :: Machine -> CBMCExceptT Errors UnionM Machine
pop = popN 1

popN :: SymInteger -> Machine -> CBMCExceptT Errors UnionM Machine
popN i (Machine p s m) = do
  st <- lift s
  mrgIf (fromIntegral (length st) <~ i) (throwError EvalError) $ do
    newst <- dropOnlyEnough st i
    return $! Machine p (mrgReturn newst) m

-- concrete pred
popUntil :: (MemValue -> Bool) -> Machine -> CBMCExceptT Errors UnionM Machine
popUntil pred (Machine p s m) = do
  st <- lift s
  newst <- computeStack st
  return $! Machine p (mrgReturn newst) m
  where
    computeStack :: [UnionM MemValue] -> CBMCExceptT Errors UnionM [UnionM MemValue]
    computeStack [] = mrgReturn []
    computeStack st@(x : xs) = do
      xv <- lift x
      if pred xv then mrgReturn st else computeStack xs

read :: SymInteger -> Machine -> CBMCExceptT Errors UnionM PCValue
read i (Machine _ _ m) = do
  m1 <- lift m
  r <- m1 !!~ i
  mrgLift r

write :: SymInteger -> PCValue -> Machine -> CBMCExceptT Errors UnionM Machine
write i v (Machine p s m) = do
  mv <- lift m
  -- mrgIf ((fromIntegral . length <$> m) <~ mrgReturn i) (throwError EvalError) $ do
  newMem <- replace mv i $ mrgReturn v
  return $! Machine p s (mrgReturn newMem)

goto :: PCValue -> Machine -> Machine
goto n (Machine _ s m) = Machine n s m

next :: Machine -> Machine
next (Machine (PCValue i l) s m) = Machine (PCValue (i + 1) l) s m
