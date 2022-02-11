{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Data.SMT.Solving
  ( solveWith,
    solveWithTranslation,
    SolverTranslation (..),
  )
where

import Control.Monad.Except
import qualified Data.HashSet as S
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as PM
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Lowering
import Grisette.Data.SymPrim
import Grisette.Data.Class.Bool
import Data.SBV.Control (Query)

solveTermWith ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  Term Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
solveTermWith config term = SBV.runSMTWith (sbvConfig config) $ do
  x <- collectPrims config term
  let (a, _) = lowerSinglePrim' config term x
  SBVC.query $ do
    SBV.constrain a
    r <- SBVC.checkSat
    case r of
      SBVC.Sat -> do
        md <- SBVC.getModel
        return $ Right $ parseModel config md x
      _ -> return $ Left r

solveWith ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  Sym Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
solveWith config (Sym t) = solveTermWith config t

class SolverTranslation method e v | method -> e v where
  errorTranslation :: method -> e -> Bool
  valueTranslation :: method -> v -> Sym Bool

translateExceptT :: (SolverTranslation method e v) => method -> ExceptT e UnionM v -> Sym Bool
translateExceptT p (ExceptT u) =
  getSingle $
    ( \case
        Left e -> conc $ errorTranslation p e
        Right v -> valueTranslation p v
    )
      <$> u

solveWithTranslation ::
  forall integerBitWidth err v method.
  (SolverTranslation method err v) =>
  method ->
  GrisetteSMTConfig integerBitWidth ->
  ExceptT err UnionM v ->
  IO (Either SBVC.CheckSatResult PM.Model)
solveWithTranslation p config e = solveWith config (translateExceptT p e)

{-
cegisWith ::
  forall integerBitWidth a. (ExtractSymbolics (S.HashSet TermSymbol) a) =>
  GrisetteSMTConfig integerBitWidth ->
  a ->
  Sym Bool ->
  Sym Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
cegisWith config foralls assumption assertion = undefined
  where
    forallSymbols :: S.HashSet TermSymbol
    forallSymbols = extractSymbolics foralls
    phi = assertion &&~ assumption
    negphi = nots assertion &&~ assumption
    q :: Model -> Query (Either SBVC.CheckSatResult PM.Model)
    q = undefined
    -}
