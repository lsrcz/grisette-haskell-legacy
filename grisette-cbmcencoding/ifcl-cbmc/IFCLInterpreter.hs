module IFCLInterpreter where

import Control.Monad.Except
import Grisette
import Instructions
import Machine
import Value
import Prelude hiding (read)

haltInst :: Machine -> Program -> CBMCExceptT Errors UnionM Machine
haltInst m p = mrgReturn $ goto (PCValue (fromIntegral $ loc p) (label $ pc m)) m

noopInst :: Machine -> CBMCExceptT Errors UnionM Machine
noopInst m = mrgReturn $ next m

pushInst :: PCValue -> Machine -> CBMCExceptT Errors UnionM Machine
pushInst p = mrgReturn . next . push (MPCValue p)

popInst :: Machine -> CBMCExceptT Errors UnionM Machine
popInst = mrgFmap next . pop

popCRInst :: Machine -> CBMCExceptT Errors UnionM Machine
popCRInst m = do
  _ <- peekPC 0 m
  mrgFmap next $ pop m

loadInst :: Machine -> CBMCExceptT Errors UnionM Machine
loadInst m = do
  PCValue x lx <- peekPC 0 m
  p <- pop m
  PCValue v lv <- read x m
  mrgReturn $ next $ push (MPCValue $ PCValue v (lx ||~ lv)) p

load1Inst :: Machine -> CBMCExceptT Errors UnionM Machine
load1Inst m = do
  PCValue x _ <- peekPC 0 m
  p <- pop m
  v <- read x m
  mrgReturn $ next $ push (MPCValue v) p

storeInst :: Machine -> CBMCExceptT Errors UnionM Machine
storeInst m = do
  PCValue x lx <- peekPC 0 m
  PCValue _ lmx <- read x m
  PCValue y ly <- peekPC 1 m
  p <- popN 2 m
  symFailIfNot EvalError (lx `implies` lmx)
  res <- write x (PCValue y (lx ||~ ly)) p
  mrgReturn $ next res

storeCRInst :: Machine -> CBMCExceptT Errors UnionM Machine
storeCRInst m = do
  let PCValue _ lpc = pc m
  PCValue x lx <- peekPC 0 m
  PCValue _ lmx <- read x m
  PCValue y ly <- peekPC 1 m
  p <- popN 2 m
  symFailIfNot EvalError ((lx ||~ lpc) `implies` lmx)
  res <- write x (PCValue y $ lx ||~ ly ||~ lpc) p
  mrgReturn $ next res

addInst :: Machine -> CBMCExceptT Errors UnionM Machine
addInst m = do
  PCValue x lx <- peekPC 0 m
  PCValue y ly <- peekPC 1 m
  p <- popN 2 m
  mrgReturn $ next $ push (MPCValue $ PCValue (x + y) (lx ||~ ly)) p

add1Inst :: Machine -> CBMCExceptT Errors UnionM Machine
add1Inst m = do
  PCValue x _ <- peekPC 0 m
  PCValue y _ <- peekPC 1 m
  p <- popN 2 m
  mrgReturn $ next $ push (MPCValue $ PCValue (x + y) $ conc False) p

store1abInst :: Machine -> CBMCExceptT Errors UnionM Machine
store1abInst m = do
  PCValue x _ <- peekPC 0 m
  y <- peekPC 1 m
  p <- popN 2 m
  res <- write x y p
  mrgReturn $ next res

store1bInst :: Machine -> CBMCExceptT Errors UnionM Machine
store1bInst m = do
  PCValue x lx <- peekPC 0 m
  PCValue y ly <- peekPC 1 m
  p <- popN 2 m
  res <- write x (PCValue y $ lx ||~ ly) p
  mrgReturn $ next res

jumpInst :: Machine -> CBMCExceptT Errors UnionM Machine
jumpInst m = do
  PCValue x lx <- peekPC 0 m
  let PCValue _ lpc = pc m
  p <- pop m
  mrgReturn $ goto (PCValue x (lx ||~ lpc)) p

jump1bInst :: Machine -> CBMCExceptT Errors UnionM Machine
jump1bInst m = do
  x <- peekPC 0 m
  p <- pop m
  mrgReturn $ goto x p

jump1abInst :: Machine -> CBMCExceptT Errors UnionM Machine
jump1abInst m = do
  PCValue x _ <- peekPC 0 m
  p <- pop m
  mrgReturn $ goto (PCValue x $ conc False) p

callInst :: PCValue -> PCValue -> Machine -> CBMCExceptT Errors UnionM Machine
callInst pos hasRet m = do
  let PCValue k lk = pos
  let PCValue vn ln = hasRet
  let PCValue vpc lpc = pc m
  PCValue x lx <- peekPC 0 m
  symFailIfNot EvalError $ nots lk
  symFailIfNot EvalError $ nots ln
  symFailIfNot EvalError $ vn ==~ 0 ||~ vn ==~ 1
  let ret = ReturnAddr (PCValue (vpc + 1) lpc) hasRet
  p <- pop m
  p1 <- pushAt k ret p
  mrgReturn $ goto (PCValue x (lx ||~ lpc)) p1

call1bInst :: PCValue -> Machine -> CBMCExceptT Errors UnionM Machine
call1bInst pos m = do
  let PCValue k lk = pos
  let PCValue vpc lpc = pc m
  PCValue x lx <- peekPC 0 m
  symFailIfNot EvalError $ nots lk
  let ret = ReturnAddr (PCValue (vpc + 1) lpc) zeroLow
  p <- pop m
  p1 <- pushAt k ret p
  mrgReturn $ goto (PCValue x (lx ||~ lpc)) p1

retInst :: Machine -> CBMCExceptT Errors UnionM Machine
retInst m = do
  let PCValue _ lpc = pc m
  PCValue v lv <- peekPC 0 m
  m1 <- popUntil (\case MPCValue {} -> False; _ -> True) m
  r <- peek 0 m1
  case r of
    MPCValue _ -> throwError EvalError
    ReturnAddr rpc (PCValue n _) -> do
      p <- pop m1
      mrgReturn $ goto rpc $ mrgIte @SymBool (n ==~ 0) p (push (MPCValue $ PCValue v (lv ||~ lpc)) p)

ret1abInst :: PCValue -> Machine -> CBMCExceptT Errors UnionM Machine
ret1abInst r m = do
  let PCValue vn ln = r
  v <- peek 0 m
  m1 <- popUntil (\case MPCValue {} -> False; _ -> True) m
  retv <- peek 0 m1
  case retv of
    MPCValue _ -> throwError EvalError
    ReturnAddr rpc _ -> do
      p <- pop m1
      symFailIfNot EvalError $ nots ln
      symFailIfNot EvalError $ vn ==~ 0 ||~ vn ==~ 1
      mrgReturn $ goto rpc $ mrgIte @SymBool (vn ==~ 0) p (push v p)

ret1bInst :: PCValue -> Machine -> CBMCExceptT Errors UnionM Machine
ret1bInst r m = do
  let PCValue vn ln = r
  let PCValue _ lpc = pc m
  PCValue v _ <- peekPC 0 m
  m1 <- popUntil (\case MPCValue {} -> False; _ -> True) m
  retv <- peek 0 m1
  case retv of
    MPCValue _ -> throwError EvalError
    ReturnAddr rpc _ -> do
      p <- pop m1
      symFailIfNot EvalError $ nots ln
      symFailIfNot EvalError $ vn ==~ 0 ||~ vn ==~ 1
      mrgReturn $ goto rpc $ mrgIte @SymBool (vn ==~ 0) p (push (MPCValue $ PCValue v lpc) p)

execInst :: Instruction -> Machine -> Program -> CBMCExceptT Errors UnionM Machine
execInst Halt m p = haltInst m p
execInst Noop m _ = noopInst m
execInst (Push v) m _ = pushInst v m
execInst Pop m _ = popInst m
execInst Store m _ = storeInst m
execInst Store1AB m _ = store1abInst m
execInst Store1B m _ = store1bInst m
execInst Load m _ = loadInst m
execInst Add m _ = addInst m
execInst Add1 m _ = add1Inst m
execInst Load1 m _ = load1Inst m
execInst Jump m _ = jumpInst m
execInst Jump1B m _ = jump1bInst m
execInst Jump1AB m _ = jump1abInst m
execInst StoreCR m _ = storeCRInst m
execInst PopCR m _ = popCRInst m
execInst Return m _ = retInst m
execInst (Return1B v) m _ = ret1bInst v m
execInst (Return1AB v) m _ = ret1abInst v m
execInst (Call1B v) m _ = call1bInst v m
execInst (Call pos hasRet) m _ = callInst pos hasRet m

step :: Int -> Machine -> Program -> CBMCExceptT Errors UnionM Machine
step k m p = mrgIf (isHalted m p ||~ conc (k == 0)) (return m) $ do
  instu <- p !!~ int (pc m)
  m1 <- lift instu >>= \inst -> execInst inst m p
  step (k - 1) m1 p
