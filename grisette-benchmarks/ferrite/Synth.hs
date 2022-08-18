{-# LANGUAGE OverloadedStrings #-}
module Synth where

import Control.Monad.State.Strict
import Data.Maybe
import Fs
import Grisette
import Interpret
import Lang
import Litmus
import Utils.Timing
import Control.DeepSeq
import Control.Monad.Except

syncCost :: [SysCall] -> SymInteger
syncCost (Efsync _ e : xs) = ites @SymBool e 1 0 + syncCost xs
syncCost (_ : xs) = syncCost xs
syncCost [] = 0

synthVCTranslation :: Either AssertionError () -> (SymBool, SymBool)
synthVCTranslation (Left _) = (conc False, conc True)
synthVCTranslation _ = (conc False, conc False)

synth ::
  forall b conc fs.
  (FileSystem conc fs, Mergeable SymBool fs, Show fs) =>
  GrisetteSMTConfig b ->
  Litmus conc fs ->
  IO (Maybe [SysCall])
synth config (Litmus fsBound make setupProc prog allowCond) =
  let fs = make
      newfs
        | not (null setupProc) = fromJust $ interpretConc setupProc fs
        | otherwise = fs
      progWithSyncs = runGenSymFresh (insertSynthSyncs fsBound prog) "syncs"
      prog1 = crack newfs progWithSyncs

      order =
        genSymSimple
          (SimpleListSpec (fromIntegral $ length prog1) (EnumGenUpperBound @Integer (fromIntegral $ length prog1)))
          "order"
      --order = [0,1,2,4,5,3,6]
      (synthFs, crashes) = runGenSymFresh (runStateT (interpretOrderOps prog1 order (mrgReturn $ (toSym newfs :: fs))) []) "crash"
      allowed = allowCond (toSym newfs) #~ synthFs

      cost = syncCost progWithSyncs
      go sol currCost =
        let costConstraint = conc (currCost == fromIntegral (length progWithSyncs)) ||~ cost <~ currCost
            synthCond :: UnionM (Either AssertionError ())
            synthCond = runExceptT $ symFailIfNot AssertionError ((validOrdering fs prog1 order `implies` allowed) &&~ costConstraint)
         in do
              _ <- timeItAll "evaluate" $ synthCond `deepseq` return ()
              m <- timeItAll "Lowering/Solving" $ cegisFallable config (crashes, order) synthVCTranslation synthCond
              case m of
                Left _ -> return sol
                Right (_, mo) -> go (Just $ evaluate True mo progWithSyncs) $ evaluate True mo cost
   in go Nothing (fromIntegral $ length progWithSyncs)
