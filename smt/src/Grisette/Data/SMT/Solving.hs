{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module Grisette.Data.SMT.Solving (solveWith) where

import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as PM
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Lowering

solveWith :: forall integerBitWidth. GrisetteSMTConfig integerBitWidth -> Term Bool -> IO PM.Model
solveWith config term = SBV.runSMTWith (sbvConfig config) $ do
  (m, a) <- lowerSinglePrim config term
  SBVC.query $ do
    SBV.constrain a
    _ <- SBVC.checkSat
    md <- SBVC.getModel
    return $ parseModel config md m
