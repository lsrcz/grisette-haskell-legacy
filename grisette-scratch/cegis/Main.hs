{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DataKinds #-}
module Main where

import Grisette
import Control.Monad.Except
import Data.Bits

data X = X

instance CegisErrorTranslation X VerificationConditions where
  cegisErrorTranslation _ = id

instance CegisTranslation X SymBool VerificationConditions () where

data Y = Y

instance CegisErrorTranslation Y VerificationConditions where
  cegisErrorTranslation _ = id

instance CegisTranslation Y SymBool VerificationConditions Integer where
  cegisValueTranslation _ i = do
    symFailIfNot AssumptionViolation (conc $ i >= 2)
    symFailIfNot AssertionViolation (conc $ odd i)
  
input :: SymUnsignedBV 4
input = ssymb "x"

input2 :: SymUnsignedBV 4
input2 = ssymb "c"

eveni :: SymUnsignedBV 4 -> Sym Bool
eveni e = e `shiftR` 1 `shiftL` 1 ==~ e

oddi :: SymUnsignedBV 4 -> Sym Bool
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
  Right (cexs, mo) <- cegisWithExcept X (UnboundedReasoning z3) input v
  print (cexs, evaluate False mo input2)
  Right (cexs1, mo1) <- cegisWithExcept X (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) m1
  print (cexs1, evaluate False mo1 m)
  Right (cexs2, mo2) <- cegisWithExcept Y (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) (lift m :: ExceptT VerificationConditions UnionM Integer)
  print (cexs2, evaluate False mo2 m)
