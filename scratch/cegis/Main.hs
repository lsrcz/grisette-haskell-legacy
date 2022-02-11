{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
module Main where

import Grisette.Core
import Grisette.SymPrim.Term
import Grisette.Backend.SBV
import Control.Monad.Except
import Data.Bits

data X = X

instance CegisTranslation X VerificationConditions () where
  cegisErrorTranslation _ = id

data Y = Y

instance CegisTranslation Y VerificationConditions Integer where
  cegisErrorTranslation _ = id
  cegisValueTranslation _ i = do
    gassertWithError AssumptionViolation (conc $ i >= 2)
    gassertWithError AssertionViolation (conc $ odd i)
  
input :: SymUnsignedBV 4
input = ssymb "x"

input2 :: SymUnsignedBV 4
input2 = ssymb "c"

eveni :: SymUnsignedBV 4 -> Sym Bool
eveni e = e `shiftR` 1 `shiftL` 1 ==~ e

oddi :: SymUnsignedBV 4 -> Sym Bool
oddi = nots . eveni

m :: UnionM Integer
m = mrgGuard (ssymb "a") (mrgGuard (ssymb "b") (mrgSingle 5) (mrgSingle 6))
                        (mrgGuard (ssymb "c") (mrgSingle 3) (mrgSingle 4))

m1 :: ExceptT VerificationConditions UnionM ()
m1 = do
  i <- lift m
  gassertWithError AssumptionViolation (conc $ i >= 2)
  gassertWithError AssertionViolation (conc $ odd i)

v :: ExceptT VerificationConditions UnionM ()
v = do
  gassertWithError AssumptionViolation (eveni input) 
  gassertWithError AssertionViolation (oddi $ input + input2) 

main :: IO()
main = do
  Right mo <- cegisWithTranslation X (UnboundedReasoning z3) input v
  print (symeval False mo input2)
  Right mo1 <- cegisWithTranslation X (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) m1
  print (symeval False mo1 m)
  Right mo2 <- cegisWithTranslation Y (UnboundedReasoning z3) (ssymb "a" :: Sym Bool) (lift m)
  print (symeval False mo2 m)
