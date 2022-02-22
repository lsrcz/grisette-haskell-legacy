{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Grisette.Data.SMT.Solving
  ( solveWith,
    solveWithTranslation,
    SolverTranslation (..),
    CegisTranslation (..),
    cegisWithTranslation,
    cegisWith,
  )
where

import Control.Monad.Except
import qualified Data.HashSet as S
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as PM
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Lowering
import Grisette.Data.SymPrim
import Grisette.Data.Class.Bool
import Data.SBV.Control (Query)
import Grisette.Data.Class.SymEval
import Grisette.Control.Exception
import Grisette.Control.Monad

solveTermWith ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  Term Bool ->
  IO (SymBiMap, Either SBVC.CheckSatResult PM.Model)
solveTermWith config term = SBV.runSMTWith (sbvConfig config) $ do
  (m, a) <- lowerSinglePrim config term
  SBVC.query $ do
    SBV.constrain a
    r <- SBVC.checkSat
    case r of
      SBVC.Sat -> do
        md <- SBVC.getModel
        return $ (m, Right $ parseModel config md m)
      _ -> return $ (m, Left r)

solveWith ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  Sym Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
solveWith config (Sym t) = snd <$> solveTermWith config t

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

class CegisTranslation method e v | method -> e v where
  cegisErrorTranslation :: method -> e -> VerificationConditions
  cegisValueTranslation :: method -> v -> ExceptT VerificationConditions UnionM ()
  default cegisValueTranslation :: (v ~ ()) => method -> v -> ExceptT VerificationConditions UnionM ()
  cegisValueTranslation _ = mrgReturn

translateCegis :: (CegisTranslation method e v)  => method -> ExceptT e UnionM v -> (Sym Bool, Sym Bool)
translateCegis p (ExceptT u) =
  getSingle $
    ( \case
        Left e -> let t = cegisErrorTranslation p e in (conc $ t == AssumptionViolation, conc $ t == AssertionViolation)
        Right v -> getSingle $ mrgFmap (\case
          Left AssumptionViolation -> (conc True, conc False)
          Left AssertionViolation -> (conc False, conc True)
          _ -> (conc False, conc False)
          ) $ runExceptT $ cegisValueTranslation p v
    )
      <$> u

cegisWithTranslation ::
  forall integerBitWidth err method a v.
  (CegisTranslation method err v, ExtractSymbolics (S.HashSet TermSymbol) a) =>
  method ->
  GrisetteSMTConfig integerBitWidth ->
  a ->
  ExceptT err UnionM v ->
  IO (Either SBVC.CheckSatResult PM.Model)
cegisWithTranslation p config foralls e =
  let
    (assumes, asserts) = translateCegis p e
   in
    cegisWith config foralls assumes asserts

cegisWith ::
  forall integerBitWidth a. (ExtractSymbolics (S.HashSet TermSymbol) a) =>
  GrisetteSMTConfig integerBitWidth ->
  a ->
  Sym Bool ->
  Sym Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
cegisWith config foralls assumption assertion = SBV.runSMTWith (sbvConfig config) $ do
  let Sym t = phi
  (newm, a) <- lowerSinglePrim config t
  SBVC.query $ snd <$>  do
    SBV.constrain a
    r <- SBVC.checkSat
    mr <- case r of
      SBVC.Sat -> do
        md <- SBVC.getModel
        return $ Right $ parseModel config md newm
      _ -> return $ Left r
    loop ((`exceptFor` forallSymbols) <$> mr) newm
  where
    forallSymbols :: S.HashSet TermSymbol
    forallSymbols = extractSymbolics foralls
    phi = nots assertion &&~ nots assumption
    negphi = assertion &&~ nots assumption
    check :: Model -> IO (Either SBVC.CheckSatResult PM.Model)
    check candidate = do
      let evaluated = symeval False candidate negphi
      r <- solveWith config evaluated
      return $ do
        m <- r
        return $ exact m forallSymbols
    guess :: Model -> SymBiMap -> Query (SymBiMap, Either SBVC.CheckSatResult PM.Model)
    guess candidate origm = do
      let Sym evaluated = symeval False candidate phi
      let (lowered, newm) = lowerSinglePrim' config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          return (newm, Right $ exceptFor model forallSymbols)
        _ -> return (newm, Left r)
    loop :: Either SBVC.CheckSatResult PM.Model -> SymBiMap ->
      Query (SymBiMap, Either SBVC.CheckSatResult PM.Model)
    loop (Right mo) origm = do
      r <- liftIO $ check mo
      case r of
        Left SBVC.Unsat -> return (origm, Right mo)
        Left _ -> return (origm, r)
        Right cex -> do
          (newm, res) <- guess cex origm
          loop res newm
    loop l@(Left _) origm = return (origm, l)

