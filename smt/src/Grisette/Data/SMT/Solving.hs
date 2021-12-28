{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module Grisette.Data.SMT.Solving (solveWith) where

import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as PM
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Lowering
import Grisette.Data.SymPrim

solveTermWith :: forall integerBitWidth. GrisetteSMTConfig integerBitWidth -> Term Bool -> IO (Either SBVC.CheckSatResult PM.Model)
solveTermWith config term = SBV.runSMTWith (sbvConfig config) $ do
  (m, a) <- lowerSinglePrim config term
  SBVC.query $ do
    SBV.constrain a
    r <- SBVC.checkSat
    case r of
      SBVC.Sat -> do
        md <- SBVC.getModel
        return $ Right $ parseModel config md m
      _ -> return $ Left r

solveWith :: forall integerBitWidth. GrisetteSMTConfig integerBitWidth -> Sym Bool -> IO (Either SBVC.CheckSatResult PM.Model)
solveWith config (Sym t) = solveTermWith config t
