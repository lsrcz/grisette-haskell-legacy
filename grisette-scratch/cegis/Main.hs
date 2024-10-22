{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Control.Monad.Except
import Data.Bits
import Grisette

data X = X

xTranslation :: Either VerificationConditions () -> (SymBool, SymBool)
xTranslation (Left AssumptionViolation) = (conc True, conc False)
xTranslation (Left AssertionViolation) = (conc False, conc True)
xTranslation _ = (conc False, conc False)

data Y = Y

yTranslation :: Either VerificationConditions Integer -> UnionM (Either VerificationConditions ())
yTranslation (Left AssumptionViolation) = return $ Left AssumptionViolation
yTranslation (Left AssertionViolation) = return $ Left AssertionViolation
yTranslation (Right i) = runExceptT $ do
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
m =
  mrgIf
    (ssymb "a")
    (mrgIf (ssymb "b") (mrgReturn 5) (mrgReturn 6))
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

main :: IO ()
main = do
  Right (cexs, mo) <- cegisFallable (UnboundedReasoning z3) input xTranslation $ runExceptT v
  print (cexs, evaluate False mo input2)
  Right (cexs1, mo1) <- cegisFallable (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) xTranslation $ runExceptT m1
  print (cexs1, evaluate False mo1 m)
  Right (cexs2, mo2) <- cegisFallable' (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) yTranslation $ runExceptT (lift m :: ExceptT VerificationConditions UnionM Integer)
  print (cexs2, evaluate False mo2 m)
