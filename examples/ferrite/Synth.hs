module Synth where

import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Maybe
import Fs
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term
import Interpret
import Lang
import Litmus

syncCost :: [SysCall] -> SymInteger
syncCost (Efsync _ e : xs) = ites @SymBool e 1 0 + syncCost xs
syncCost (_ : xs) = syncCost xs
syncCost [] = 0

data Synth = Synth

instance CegisTranslation Synth AssertionError () where
  cegisErrorTranslation _ _ = AssertionViolation

synth ::
  forall b conc fs.
  (FileSystem conc fs, Mergeable SymBool fs, Show fs) =>
  GrisetteSMTConfig b ->
  Litmus conc fs ->
  IO (Maybe [SysCall])
synth config (Litmus fsBound make setupProc prog allowCond) =
  let fs = make
      newfs =
        if length setupProc > 0
          then fromJust $ interpretConc setupProc fs
          else fs
      progWithSyncs = runSymGenIndexed' (insertSynthSyncs fsBound prog) "syncs"
      prog1 = crack newfs progWithSyncs

      order :: [UnionM Integer]
      order =
        genSymSimple @SymBool
          ( SimpleListSpec (fromIntegral $ length prog1) (IntegerGenUpperBound (fromIntegral $ length prog1))
          )
          "order"
      --order = [0,1,2,4,5,3,6]
      (synthFs, (_, crashes)) = runState (interpretOrderOps prog1 order (mrgSingle $ (toSym newfs :: fs))) ((0, "crash"), [])
      allowed = allowCond (toSym newfs) #~ synthFs

      cost = syncCost progWithSyncs
      go :: Maybe [SysCall] -> SymInteger -> IO (Maybe [SysCall])
      go sol currCost =
        let costConstraint :: SymBool
            costConstraint =
              if currCost == fromIntegral (length progWithSyncs) then conc True else cost <~ currCost
            synthCond :: ExceptT AssertionError UnionM ()
            synthCond = gassertWithError AssertionError ((validOrdering fs prog1 order `implies` allowed) &&~ costConstraint)
         in do
              m <- cegisWithTranslation Synth config (crashes, order) synthCond
              case m of
                Left _ -> return sol
                Right mo -> do
                  let s = symeval True mo progWithSyncs
                  let c = symeval True mo cost
                  go (Just s) c
   in go Nothing (fromIntegral $ length progWithSyncs)
