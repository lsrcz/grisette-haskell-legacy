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
import Grisette.Unordered.UUnionM

data Verify = Verify

instance ToAssertion Verify SymBool (Either AssertionError ()) where
  toAssertion _ (Left _) = conc True
  toAssertion _ (Right _) = conc False

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
        genSymSimple
          (SimpleListSpec (fromIntegral $ length prog1) (EnumGenUpperBound @Integer (fromIntegral $ length prog1)))
          "order"

      (verifFs, _) = runGenSymFresh (runStateT (interpretOrderOps prog1 order (mrgReturn $ (toSym newfs :: fs))) []) "crash"
      allowed = allowCond (toSym newfs) #~ verifFs

      verifCond :: UnionM (Either AssertionError ())
      verifCond = runExceptT $ symFailIfNot AssertionError (validOrdering fs prog1 order `implies` allowed)
   in do
        _ <- timeItAll "evaluate" $ verifCond `deepseq` return ()
        r <- timeItAll "Lowering/Solving" $ solve Verify config verifCond
        case r of
          Left _ -> return Nothing
          Right mo -> return $ (case evaluate True mo verifFs of; SingleU v -> Just v; _ -> Nothing) >>= toCon