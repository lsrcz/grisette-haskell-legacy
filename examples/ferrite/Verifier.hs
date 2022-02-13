module Verifier where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Maybe
import Fs
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Interpret
import Litmus

data Verify = Verify

instance SolverTranslation Verify AssertionError () where
  errorTranslation _ _ = True
  valueTranslation _ _ = conc False

verify ::
  forall b conc fs.
  (FileSystem conc fs, Mergeable SymBool fs, Show fs) =>
  GrisetteSMTConfig b ->
  Litmus conc fs ->
  IO (Maybe conc)
verify config (Litmus _ make setupProc prog allowCond) =
  let fs = make
      newfs =
        if not (null setupProc)
          then fromJust $ interpretConc setupProc fs
          else fs
      prog1 = crack newfs prog
      order :: [UnionM Integer]
      order =
        genSymSimple @SymBool
          ( SimpleListSpec (fromIntegral $ length prog1) (IntegerGenUpperBound (fromIntegral $ length prog1))
          )
          "order"

      (verifFs, _) = runState (interpretOrderOps prog1 order (mrgSingle $ (toSym newfs :: fs))) ((0, "crash"), [])
      allowed = allowCond (toSym newfs) #~ verifFs

      verifCond :: ExceptT AssertionError UnionM ()
      verifCond = gassertWithError AssertionError (validOrdering fs prog1 order `implies` allowed)
   in do
        r <- solveWithTranslation Verify config verifCond
        case r of
          Left _ -> return Nothing
          Right mo -> return $ toCon $ symeval True mo verifFs