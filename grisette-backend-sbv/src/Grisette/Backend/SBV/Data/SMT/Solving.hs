{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Backend.SBV.Data.SMT.Solving
  ( DefaultVerificationCondition (..),
  )
where

import Control.Monad.Except
import qualified Data.HashSet as S
import Data.Maybe
import qualified Data.SBV as SBV
import Data.SBV.Control (Query)
import qualified Data.SBV.Control as SBVC
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Evaluate
import Grisette.Core.Data.Class.ExtractSymbolics
import Grisette.Core.Data.Class.Solver
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.InternedTerm
import Grisette.IR.SymPrim.Data.Prim.Model as PM
import Grisette.Backend.SBV.Data.SMT.Config
import Grisette.Backend.SBV.Data.SMT.Lowering
import Grisette.IR.SymPrim.Data.SymPrim
import Grisette.Core.Control.Exception
import Grisette.Core.Data.Class.PrimWrapper

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

instance Solver (GrisetteSMTConfig n) SymBool (S.HashSet TermSymbol) SBVC.CheckSatResult PM.Model where
  solveFormula config (Sym t) = snd <$> solveTermWith config t
  solveFormulaMulti config n s@(Sym t)
    | n > 0 = SBV.runSMTWith (sbvConfig config) $ do
      (newm, a) <- lowerSinglePrim config t
      SBVC.query $ do
        SBV.constrain a
        r <- SBVC.checkSat
        case r of
          SBVC.Sat -> do
            md <- SBVC.getModel
            let model = parseModel config md newm
            remainingModels n model newm
          _ -> return []
    | otherwise = return []
    where
      allSymbols = extractSymbolics s :: S.HashSet TermSymbol
      next :: PM.Model -> SymBiMap -> Query (SymBiMap, Either SBVC.CheckSatResult PM.Model)
      next md origm = do
        let newtm = S.foldl' (\acc v -> orb acc (notb (fromJust $ equation md v))) (concTerm False) allSymbols
        let (lowered, newm) = lowerSinglePrim' config newtm origm
        SBV.constrain lowered
        r <- SBVC.checkSat
        case r of
          SBVC.Sat -> do
            md1 <- SBVC.getModel
            let model = parseModel config md1 newm
            return (newm, Right model)
          _ -> return (newm, Left r)
      remainingModels :: Int -> PM.Model -> SymBiMap -> Query [PM.Model]
      remainingModels n1 md origm
        | n1 > 1 = do
          (newm, r) <- next md origm
          case r of
            Left _ -> return [md]
            Right mo -> do
              rmmd <- remainingModels (n1 - 1) mo newm
              return $ md : rmmd
        | otherwise = return [md]
  solveFormulaAll = undefined
  cegisFormulas :: forall forallArg. (ExtractSymbolics (S.HashSet TermSymbol) forallArg, Evaluate PM.Model forallArg) =>
   GrisetteSMTConfig n -> forallArg -> SymBool -> SymBool -> IO (Either SBVC.CheckSatResult ([forallArg], PM.Model))
  cegisFormulas config foralls assumption assertion = SBV.runSMTWith (sbvConfig config) $ do
    let Sym t = phi
    (newm, a) <- lowerSinglePrim config t
    SBVC.query $
      snd <$> do
        SBV.constrain a
        r <- SBVC.checkSat
        mr <- case r of
          SBVC.Sat -> do
            md <- SBVC.getModel
            return $ Right $ parseModel config md newm
          _ -> return $ Left r
        loop ((`exceptFor` forallSymbols) <$> mr) [] newm
    where
      forallSymbols :: S.HashSet TermSymbol
      forallSymbols = extractSymbolics foralls
      phi = nots assertion &&~ nots assumption
      negphi = assertion &&~ nots assumption
      check :: Model -> IO (Either SBVC.CheckSatResult (forallArg, PM.Model))
      check candidate = do
        let evaluated = evaluate False candidate negphi
        r <- solveFormula config evaluated
        return $ do
          m <- r
          let newm = exact m forallSymbols
          return (evaluate False newm foralls, newm)
      guess :: Model -> SymBiMap -> Query (SymBiMap, Either SBVC.CheckSatResult PM.Model)
      guess candidate origm = do
        let Sym evaluated = evaluate False candidate phi
        let (lowered, newm) = lowerSinglePrim' config evaluated origm
        SBV.constrain lowered
        r <- SBVC.checkSat
        case r of
          SBVC.Sat -> do
            md <- SBVC.getModel
            let model = parseModel config md newm
            return (newm, Right $ exceptFor model forallSymbols)
          _ -> return (newm, Left r)
      loop ::
        Either SBVC.CheckSatResult PM.Model ->
        [forallArg] ->
        SymBiMap ->
        Query (SymBiMap, Either SBVC.CheckSatResult ([forallArg], PM.Model))
      loop (Right mo) cexs origm = do
        r <- liftIO $ check mo
        case r of
          Left SBVC.Unsat -> return (origm, Right (cexs, mo))
          Left v -> return (origm, Left v)
          Right (cex, cexm) -> do
            (newm, res) <- guess cexm origm
            loop res (cex : cexs) newm
      loop (Left v) _ origm = return (origm, Left v)

data DefaultVerificationCondition = DefaultVerificationCondition

instance SolverErrorTranslation DefaultVerificationCondition VerificationConditions where
  errorTranslation _ AssumptionViolation = False
  errorTranslation _ AssertionViolation = True

instance SymBoolOp bool => SolverTranslation DefaultVerificationCondition bool VerificationConditions () where
  valueTranslation _ _ = conc False

instance CegisErrorTranslation DefaultVerificationCondition VerificationConditions where
  cegisErrorTranslation _ = id

instance (SymBoolOp bool) =>
  CegisTranslation DefaultVerificationCondition bool VerificationConditions () where
  
{-
solveWith ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  Sym Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
solveWith config (Sym t) = snd <$> solveTermWith config t

solveArgWith ::
  forall integerBitWidth spec a.
  (GenSym SymBool spec a, Evaluate Model a, ExtractSymbolics (S.HashSet TermSymbol) a) =>
  GrisetteSMTConfig integerBitWidth ->
  spec ->
  (a -> Sym Bool) ->
  IO (Either SBVC.CheckSatResult (a, PM.Model))
solveArgWith config argSpec func =
  let args = genSym argSpec (nameWithInfo "arg" CegisInternal) :: UnionM a
   in do
        r <- solveWith config (func #~ args)
        case r of
          Left csr -> return $ Left csr
          Right mo -> do
            let rmo = extendTo mo (extractSymbolics args)
            return $
              Right
                ( case evaluate False rmo args of
                    SingleU v -> v
                    _ -> error "Should not happen",
                  rmo
                )

solveMultiWith ::
  forall integerBitWidth.
  GrisetteSMTConfig integerBitWidth ->
  Int ->
  Sym Bool ->
  IO [PM.Model]
solveMultiWith config n s@(Sym t)
  | n > 0 = SBV.runSMTWith (sbvConfig config) $ do
    (newm, a) <- lowerSinglePrim config t
    SBVC.query $ do
      SBV.constrain a
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          remainingModels n model newm
        _ -> return []
  | otherwise = return []
  where
    allSymbols = extractSymbolics s :: S.HashSet TermSymbol
    next :: PM.Model -> SymBiMap -> Query (SymBiMap, Either SBVC.CheckSatResult PM.Model)
    next md origm = do
      let newtm = S.foldl' (\acc v -> orb acc (notb (fromJust $ equation md v))) (concTerm False) allSymbols
      let (lowered, newm) = lowerSinglePrim' config newtm origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md1 <- SBVC.getModel
          let model = parseModel config md1 newm
          return (newm, Right model)
        _ -> return (newm, Left r)
    remainingModels :: Int -> PM.Model -> SymBiMap -> Query [PM.Model]
    remainingModels n1 md origm
      | n1 > 1 = do
        (newm, r) <- next md origm
        case r of
          Left _ -> return [md]
          Right mo -> do
            rmmd <- remainingModels (n1 - 1) mo newm
            return $ md : rmmd
      | otherwise = return [md]

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

solveArgWithTranslation ::
  forall integerBitWidth err v method spec a.
  (SolverTranslation method err v, GenSym SymBool spec a, Evaluate Model a, ExtractSymbolics (S.HashSet TermSymbol) a) =>
  method ->
  GrisetteSMTConfig integerBitWidth ->
  spec ->
  (a -> ExceptT err UnionM v) ->
  IO (Either SBVC.CheckSatResult (a, PM.Model))
solveArgWithTranslation p config argSpec f = solveArgWith config argSpec (translateExceptT p . f)

solveWithTranslation ::
  forall integerBitWidth err v method.
  (SolverTranslation method err v) =>
  method ->
  GrisetteSMTConfig integerBitWidth ->
  ExceptT err UnionM v ->
  IO (Either SBVC.CheckSatResult PM.Model)
solveWithTranslation p config e = solveWith config (translateExceptT p e)

solveMultiWithTranslation ::
  forall integerBitWidth err v method.
  (SolverTranslation method err v) =>
  method ->
  GrisetteSMTConfig integerBitWidth ->
  Int ->
  ExceptT err UnionM v ->
  IO [PM.Model]
solveMultiWithTranslation p config n e = solveMultiWith config n (translateExceptT p e)

{-class CegisTranslation method e v | method -> e v where
  cegisErrorTranslation :: method -> e -> VerificationConditions
  cegisValueTranslation :: method -> v -> ExceptT VerificationConditions UnionM ()
  default cegisValueTranslation :: (v ~ ()) => method -> v -> ExceptT VerificationConditions UnionM ()
  cegisValueTranslation _ = mrgReturn
  -}

data DefaultVerificationCondition = DefaultVerificationCondition

{-instance CegisTranslation DefaultVerificationCondition VerificationConditions () where
  cegisErrorTranslation _ = id
  -}

translateCegis :: (CegisTranslation method e v) => method -> ExceptT e UnionM v -> (Sym Bool, Sym Bool)
translateCegis p (ExceptT u) =
  getSingle $
    ( \case
        Left e -> let t = cegisErrorTranslation p e in (conc $ t == AssumptionViolation, conc $ t == AssertionViolation)
        Right v ->
          getSingle $
            mrgFmap
              ( \case
                  Left AssumptionViolation -> (conc True, conc False)
                  Left AssertionViolation -> (conc False, conc True)
                  _ -> (conc False, conc False)
              )
              $ runExceptT $ cegisValueTranslation p v
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
  let (assumes, asserts) = translateCegis p e
   in cegisWith config foralls assumes asserts

cegisWith ::
  forall integerBitWidth a.
  (ExtractSymbolics (S.HashSet TermSymbol) a) =>
  GrisetteSMTConfig integerBitWidth ->
  a ->
  Sym Bool ->
  Sym Bool ->
  IO (Either SBVC.CheckSatResult PM.Model)
cegisWith config foralls assumption assertion = SBV.runSMTWith (sbvConfig config) $ do
  let Sym t = phi
  (newm, a) <- lowerSinglePrim config t
  SBVC.query $
    snd <$> do
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
      let evaluated = evaluate False candidate negphi
      r <- solveWith config evaluated
      return $ do
        m <- r
        return $ exact m forallSymbols
    guess :: Model -> SymBiMap -> Query (SymBiMap, Either SBVC.CheckSatResult PM.Model)
    guess candidate origm = do
      let Sym evaluated = evaluate False candidate phi
      let (lowered, newm) = lowerSinglePrim' config evaluated origm
      SBV.constrain lowered
      r <- SBVC.checkSat
      case r of
        SBVC.Sat -> do
          md <- SBVC.getModel
          let model = parseModel config md newm
          return (newm, Right $ exceptFor model forallSymbols)
        _ -> return (newm, Left r)
    loop ::
      Either SBVC.CheckSatResult PM.Model ->
      SymBiMap ->
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

data CegisInternal = CegisInternal deriving (Eq, Show, Ord, Generic, Hashable, Lift, NFData)

cegisWithTranslation' ::
  forall integerBitWidth err method spec a v.
  ( CegisTranslation method err v,
    ExtractSymbolics (S.HashSet TermSymbol) a,
    GenSym SymBool spec a,
    Mergeable SymBool err,
    Mergeable SymBool v
  ) =>
  method ->
  GrisetteSMTConfig integerBitWidth ->
  spec ->
  (a -> ExceptT err UnionM v) ->
  IO (Either SBVC.CheckSatResult PM.Model)
cegisWithTranslation' p config inputSpec f =
  let args = genSym inputSpec (nameWithInfo "arg" CegisInternal) :: UnionM a
   in cegisWithTranslation p config args (f #~ args)

cegisWith' ::
  forall integerBitWidth spec a.
  (ExtractSymbolics (S.HashSet TermSymbol) a, GenSym SymBool spec a) =>
  GrisetteSMTConfig integerBitWidth ->
  spec ->
  (a -> Sym Bool) ->
  (a -> Sym Bool) ->
  IO (Either SBVC.CheckSatResult PM.Model)
cegisWith' config inputSpec assumption assertion =
  let args = genSym inputSpec (nameWithInfo "arg" CegisInternal) :: UnionM a
   in cegisWith config args (assumption #~ args) (assertion #~ args)

-}