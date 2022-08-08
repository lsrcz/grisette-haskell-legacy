{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DataKinds #-}
module Main where

import Grisette
import Control.Monad.Except
import Data.Bits

data X = X

instance ToVC X SymBool (Either VerificationConditions ()) where
  toVCBoolPair _ (Left AssumptionViolation) = (conc True, conc False)
  toVCBoolPair _ (Left AssertionViolation) = (conc False, conc True)
  toVCBoolPair _ _ = (conc False, conc False)

data Y = Y

instance ToVC Y SymBool (Either VerificationConditions Integer) where
  toVCBoolPair _ (Left AssumptionViolation) = (conc True, conc False)
  toVCBoolPair _ (Left AssertionViolation) = (conc False, conc True)
  toVCBoolPair _ (Right i) = vcToBoolPair $ runExceptT $ do
    symFailIfNot AssumptionViolation (conc $ i >= 2)
    symFailIfNot AssertionViolation (conc $ odd i) :: ExceptT VerificationConditions UnionM ()
  
input :: SymWordN 4
input = ssymb "x"

input2 :: SymWordN 4
input2 = ssymb "c"

eveni :: SymWordN 4 -> Sym Bool
eveni e = e `shiftR` 1 `shiftL` 1 ==~ e

oddi :: SymWordN 4 -> Sym Bool
oddi = nots . eveni

m :: UnionM Integer
m = mrgIf (ssymb "a") (mrgIf (ssymb "b") (mrgReturn 5) (mrgReturn 6))
                        (mrgIf (ssymb "c") (mrgReturn 3) (mrgReturn 4))

m1 :: ExceptT VerificationConditions UnionM ()
m1 = do
  i <- lift m
  symFailIfNot AssumptionViolation (conc $ i >= 2)
  symFailIfNot AssertionViolation (conc $ odd i)

v :: ExceptT VerificationConditions UnionM ()
v = do
  symFailIfNot AssumptionViolation (eveni input) 
  symFailIfNot AssertionViolation (oddi $ input + input2) 

main :: IO()
main = do
  Right (cexs, mo) <- cegis X (UnboundedReasoning z3) input $ runExceptT v
  print (cexs, evaluate False mo input2)
  Right (cexs1, mo1) <- cegis X (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) $ runExceptT m1
  print (cexs1, evaluate False mo1 m)
  Right (cexs2, mo2) <- cegis Y (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) $ runExceptT (lift m :: ExceptT VerificationConditions UnionM Integer)
  print (cexs2, evaluate False mo2 m)
