{-# LANGUAGE OverloadedStrings #-}
module Verifier where

import Control.Monad.State.Strict
import Data.Maybe
import Fs
import Grisette
import Interpret
import Litmus
import Utils.Timing
import Control.DeepSeq
import Control.Monad.Except

data Verify = Verify

instance SolverErrorTranslation Verify AssertionError where
  errorTranslation _ _ = True

instance SolverTranslation Verify SymBool AssertionError () where
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
      order =
        genSymSimple @SymBool
          (SimpleListSpec (fromIntegral $ length prog1) (NumGenUpperBound @Integer (fromIntegral $ length prog1 - 1)))
          "order"

      (verifFs, _) = runGenSymFresh (runStateT (interpretOrderOps prog1 order (mrgReturn $ (toSym newfs :: fs))) []) "crash"
      allowed = allowCond (toSym newfs) #~ verifFs

      verifCond = symFailIfNot AssertionError (validOrdering fs prog1 order `implies` allowed)
   in do
        _ <- timeItAll "evaluate" $ (runExceptT verifCond) `deepseq` return ()
        r <- timeItAll "Lowering/Solving" $ solveWithExcept Verify config verifCond
        case r of
          Left _ -> return Nothing
          Right mo -> return $ (case evaluate True mo verifFs of; SingleU v -> Just v; _ -> Nothing) >>= toCon