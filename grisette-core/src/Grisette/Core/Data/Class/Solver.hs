{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Grisette.Core.Data.Class.Solver
  ( SolverErrorTranslation (..),
    SolverTranslation (..),
    CegisErrorTranslation (..),
    CegisTranslation (..),
    Solver (..),
    {-
    SolveProblem
      ( Formula,
        WithExcept,
        ArgFormula,
        ArgWithExcept
      ),
    solve,
    CegisProblem
      ( CFormulaPair,
        CArgFormulaPair,
        CForallFormulaPair,
        CArgForallFormulaPair,
        CWithExcept,
        CArgWithExcept,
        CForallWithExcept,
        CArgForallWithExcept
      ),
    cegis,
    forallIn,
    argBy,
    forallBy,
    translateBy,
    -}
    solveWithExcept,
    solveArgWithExcept,
    solveWithExceptMulti,
    cegisWithExcept,
    cegisForallByWithExcept,
    cegisArgWithExcept,
    cegisArgForallByWithExcept,
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Data.Hashable
import Generics.Deriving
import Grisette.Core.Control.Exception
import Grisette.Core.Control.Monad.UnionMBase
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Evaluate
import Grisette.Core.Data.Class.ExtractSymbolics
import Grisette.Core.Data.Class.GenSym
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.PrimWrapper
import Grisette.Core.Data.Class.SimpleMergeable
import Language.Haskell.TH.Syntax

class SolverErrorTranslation spec e | spec -> e where
  errorTranslation :: spec -> e -> Bool

class (SymBoolOp bool, SolverErrorTranslation spec e) => SolverTranslation spec bool e v | spec bool -> e where
  valueTranslation :: spec -> v -> bool

class CegisErrorTranslation spec e | spec -> e where
  cegisErrorTranslation :: spec -> e -> VerificationConditions

class (SymBoolOp bool, CegisErrorTranslation spec e) => CegisTranslation spec bool e v | spec -> e v where
  cegisValueTranslation :: (MonadError VerificationConditions u, UnionLike bool u) => spec -> v -> u ()
  default cegisValueTranslation :: (MonadError VerificationConditions u, UnionLike bool u, v ~ ()) => spec -> v -> u ()
  cegisValueTranslation _ = mrgSingle

translateExceptT :: (SolverTranslation spec bool e v, UnionPrjOp bool u, Functor u) => spec -> ExceptT e u v -> bool
translateExceptT p (ExceptT u) =
  getSingle $
    ( \case
        Left e -> conc $ errorTranslation p e
        Right v -> valueTranslation p v
    )
      <$> u

translateCegis :: forall spec bool u e v. (CegisTranslation spec bool e v, UnionPrjOp bool u, Monad u) => spec -> ExceptT e u v -> (bool, bool)
translateCegis p (ExceptT u) =
  getSingle $
    ( \case
        Left e -> let t = cegisErrorTranslation p e in (conc $ t == AssumptionViolation, conc $ t == AssertionViolation)
        Right v ->
          getSingle $
            fmap
              ( \case
                  Left AssumptionViolation -> (conc True, conc False)
                  Left AssertionViolation -> (conc False, conc True)
                  _ -> (conc False, conc False)
              )
              (runExceptT $ cegisValueTranslation p v :: u (Either VerificationConditions ()))
    )
      <$> u

data SolveInternal = SolveInternal deriving (Eq, Show, Ord, Generic, Hashable, Lift, NFData)

class
  (SymBoolOp bool, Evaluate model bool) =>
  Solver config bool symbolSet failure model
    | config -> bool symbolSet failure model
  where
  solveFormula :: config -> bool -> IO (Either failure model)
  solveFormulaMulti :: config -> Int -> bool -> IO [model]
  solveFormulaAll :: config -> Int -> bool -> IO [model]
  cegisFormulas ::
    (Evaluate model forallArg, ExtractSymbolics symbolSet forallArg) =>
    config ->
    forallArg ->
    bool ->
    bool ->
    IO (Either failure ([forallArg], model))

  solveArgFormula ::
    forall spec arg.
    (GenSym bool spec arg, Evaluate model arg, ExtractSymbolics symbolSet arg) =>
    config ->
    spec ->
    (arg -> bool) ->
    IO (Either failure (arg, model))
  solveArgFormula config argSpec func =
    let args = genSym argSpec (nameWithInfo "arg" SolveInternal) :: UnionMBase bool arg
     in do
          r <- solveFormula config (func #~ args)
          case r of
            Left csr -> return $ Left csr
            Right mo -> do
              return $
                Right
                  ( case evaluate True mo args of
                      SingleU v -> v
                      _ -> error "Should not happen",
                    mo
                  )
  cegisForallByFormulas ::
    forall spec a.
    (ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet bool, GenSym bool spec a, Evaluate model a) =>
    config ->
    spec ->
    (a -> (bool, bool)) ->
    IO (Either failure ([a], model))
  cegisForallByFormulas config forallSpec formulas =
    let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool a
     in do
          r <- uncurry (cegisFormulas config forallArgs) (formulas #~ forallArgs)
          case r of
            Left err -> return $ Left err
            Right (v, model) -> return $ Right ((\(SingleU vs) -> vs) <$> v, model)
  cegisArgFormulas ::
    forall forallArg argSpec arg.
    (ExtractSymbolics symbolSet forallArg, GenSym bool argSpec arg, Evaluate model arg, Evaluate model forallArg) =>
    config ->
    forallArg ->
    argSpec ->
    (arg -> (bool, bool)) ->
    IO (Either failure (arg, [forallArg], model))
  cegisArgFormulas config forallArg argSpec formulas =
    let args = genSym argSpec (nameWithInfo "arg" SolveInternal) :: UnionMBase bool arg
     in do
          r <- uncurry (cegisFormulas config forallArg) (formulas #~ args)
          case r of
            Left csr -> return $ Left csr
            Right (forallArgRet, mo) -> do
              return $
                Right
                  ( case evaluate True mo args of
                      SingleU v -> v
                      _ -> error "Should not happen",
                    forallArgRet,
                    mo
                  )
  cegisArgForallByFormulas ::
    forall forallSpec forallArg argSpec arg.
    ( ExtractSymbolics symbolSet forallArg,
      ExtractSymbolics symbolSet bool,
      GenSym bool forallSpec forallArg,
      GenSym bool argSpec arg,
      Evaluate model arg,
      Evaluate model forallArg
    ) =>
    config ->
    forallSpec ->
    argSpec ->
    (arg -> forallArg -> (bool, bool)) ->
    IO (Either failure (arg, [forallArg], model))
  cegisArgForallByFormulas config forallSpec argSpec formulas =
    let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool forallArg
     in do
          r <- cegisArgFormulas config forallArgs argSpec (flip formulas #~ forallArgs)
          case r of
            Left err -> return $ Left err
            Right (arg, forallArgRet, model) -> return $ Right (arg, (\(SingleU v) -> v) <$> forallArgRet, model)

solveWithExcept ::
  ( SolverTranslation spec bool err v,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Functor u
  ) =>
  spec ->
  config ->
  ExceptT err u v ->
  IO (Either failure model)
solveWithExcept spec config e = solveFormula config (translateExceptT spec e)

solveArgWithExcept ::
  ( SolverTranslation spec bool err v,
    GenSym bool argSpec arg,
    Evaluate model arg,
    ExtractSymbolics symbolSet arg,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Functor u
  ) =>
  spec ->
  config ->
  argSpec ->
  (arg -> ExceptT err u v) ->
  IO (Either failure (arg, model))
solveArgWithExcept spec config argSpec f = solveArgFormula config argSpec (translateExceptT spec . f)

solveWithExceptMulti ::
  ( SolverTranslation spec bool err v,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Functor u
  ) =>
  spec ->
  config ->
  Int ->
  ExceptT err u v ->
  IO [model]
solveWithExceptMulti spec config n e = solveFormulaMulti config n (translateExceptT spec e)

cegisWithExcept ::
  ( CegisTranslation spec bool err v,
    ExtractSymbolics symbolSet forallArgs,
    Evaluate model forallArgs,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Monad u
  ) =>
  spec ->
  config ->
  forallArgs ->
  ExceptT err u v ->
  IO (Either failure ([forallArgs], model))
cegisWithExcept p config foralls e =
  let (assumes, asserts) = translateCegis p e
   in cegisFormulas config foralls assumes asserts

cegisForallByWithExcept ::
  forall config bool u spec err v symbolSet a forallSpec model failure.
  ( CegisTranslation spec bool err v,
    ExtractSymbolics symbolSet a,
    ExtractSymbolics symbolSet bool,
    GenSym bool forallSpec a,
    Mergeable bool err,
    Mergeable bool v,
    Evaluate model a,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Monad u
  ) =>
  spec ->
  config ->
  forallSpec ->
  (a -> ExceptT err u v) ->
  IO (Either failure ([a], model))
cegisForallByWithExcept p config forallSpec f =
  let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool a
   in do
        r <- cegisWithExcept p config forallArgs (f #~ forallArgs)
        case r of
          Left err -> return $ Left err
          Right (v, model) -> return $ Right ((\(SingleU vs) -> vs) <$> v, model)

cegisArgWithExcept ::
  forall config bool u spec err v symbolSet forallArgs model failure argSpec arg.
  ( CegisTranslation spec bool err v,
    ExtractSymbolics symbolSet forallArgs,
    GenSym bool argSpec arg,
    Mergeable bool v,
    Mergeable bool err,
    Evaluate model arg,
    Evaluate model forallArgs,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Monad u
  ) =>
  spec ->
  config ->
  forallArgs ->
  argSpec ->
  (arg -> ExceptT err u v) ->
  IO (Either failure (arg, [forallArgs], model))
cegisArgWithExcept p config foralls argSpec f =
  let args = genSym argSpec (nameWithInfo "arg" SolveInternal) :: UnionMBase bool arg
      (assumes, asserts) = translateCegis p (f #~ args) :: (bool, bool)
   in do
        r <- cegisFormulas config foralls assumes asserts
        case r of
          Left csr -> return $ Left csr
          Right (forallArgs, mo) -> do
            return $
              Right
                ( case evaluate True mo args of
                    SingleU v -> v
                    _ -> error "Should not happen",
                  forallArgs,
                  mo
                )

cegisArgForallByWithExcept ::
  forall config bool u spec err v symbolSet forallArg forallSpec argSpec arg model failure.
  ( CegisTranslation spec bool err v,
    ExtractSymbolics symbolSet forallArg,
    ExtractSymbolics symbolSet bool,
    GenSym bool forallSpec forallArg,
    GenSym bool argSpec arg,
    Mergeable bool err,
    Mergeable bool v,
    Evaluate model arg,
    Evaluate model forallArg,
    Solver config bool symbolSet failure model,
    UnionPrjOp bool u,
    Monad u
  ) =>
  spec ->
  config ->
  forallSpec ->
  argSpec ->
  (arg -> forallArg -> ExceptT err u v) ->
  IO (Either failure (arg, [forallArg], model))
cegisArgForallByWithExcept p config forallSpec argSpec f =
  let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool forallArg
   in do
        r <- cegisArgWithExcept p config forallArgs argSpec (flip f #~ forallArgs)
        case r of
          Left err -> return $ Left err
          Right (v, forallArgsRet, model) -> return $ Right (v, (\(SingleU vs) -> vs) <$> forallArgsRet, model)

{-
data
  SolveProblem
    bool
    symbolSet
    model
    (unResolvedArg :: Bool)
    (haveArg :: Bool)
    (argType :: Data.Kind.Type)
    (translate :: Bool)
    err
    v
  where
  Formula :: bool -> SolveProblem bool symbolSet model 'False 'False () 'False () ()
  WithExcept :: ExceptT err (UnionMBase bool) v -> SolveProblem bool symbolSet model 'False 'False () 'True err v
  ArgFormula :: (arg -> bool) -> SolveProblem bool symbolSet model 'True 'True arg 'False () ()
  ArgWithExcept ::
    (arg -> ExceptT err (UnionMBase bool) v) ->
    SolveProblem bool symbolSet model 'True 'True arg 'True err v
  WithArgSpec ::
    (GenSym bool argSpec argType, Evaluate model argType, ExtractSymbolics symbolSet argType) =>
    argSpec ->
    SolveProblem bool symbolSet model 'True 'True argType translate err v ->
    SolveProblem bool symbolSet model 'False 'True argType translate err v
  WithTranslate ::
    (SolverTranslation spec bool err v) =>
    spec ->
    SolveProblem bool symbolSet model unResolvedArg haveArg argType 'True err v ->
    SolveProblem bool symbolSet model unResolvedArg haveArg argType 'False err v

type family SolveResult failure model arg haveArg where
  SolveResult failure model arg 'True = IO (Either failure (arg, model))
  SolveResult failure model arg 'False = IO (Either failure model)

solve ::
  Solver config bool symbolSet failure model =>
  config ->
  SolveProblem bool symbolSet model 'False haveArg argType 'False err v ->
  SolveResult failure model argType haveArg
solve config (Formula v) = solveFormula config v
solve config (WithArgSpec argSpec (ArgFormula v)) = solveArgFormula config argSpec v
solve config (WithTranslate spec (WithExcept v)) = solveWithExcept spec config v
solve config (WithArgSpec argSpec (WithTranslate spec (ArgWithExcept v))) =
  solveArgWithExcept spec config argSpec v
solve config (WithTranslate spec (WithArgSpec argSpec (ArgWithExcept v))) =
  solveArgWithExcept spec config argSpec v

data
  CegisProblem
    bool
    u
    symbolSet
    model
    (unResolvedArg :: Bool)
    (haveArg :: Bool)
    arg
    (unResolvedForallIn :: Bool)
    forallIn
    (unResolvedForallArg :: Bool)
    forallArg
    (haveForallIn :: Bool)
    (translate :: Bool)
    err
    v
  where
  CFormulaPair :: bool -> bool -> CegisProblem bool u symbolSet model 'False 'False () 'True () 'False () 'True 'False () ()
  CWithExcept ::
    ExceptT err u v ->
    CegisProblem bool u symbolSet model 'False 'False () 'True () 'False () 'True 'True err v
  CArgFormulaPair ::
    (arg -> (bool, bool)) ->
    CegisProblem bool u symbolSet model 'True 'True arg 'True () 'False () 'True 'False () ()
  CForallFormulaPair ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg) =>
    (forallArg -> (bool, bool)) ->
    CegisProblem bool u symbolSet model 'False 'False () 'False () 'True forallArg 'False 'False () ()
  CArgForallFormulaPair ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg) =>
    (arg -> forallArg -> (bool, bool)) ->
    CegisProblem bool u symbolSet model 'True 'True arg 'False () 'True forallArg 'False 'False () ()
  CArgWithExcept ::
    (arg -> ExceptT err u v) ->
    CegisProblem bool u symbolSet model 'True 'True arg 'True () 'False () 'True 'True err v
  CForallWithExcept ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg) =>
    (forallArg -> ExceptT err u v) ->
    CegisProblem bool u symbolSet model 'False 'False () 'False () 'True forallArg 'False 'True err v
  CArgForallWithExcept ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg, ExtractSymbolics symbolSet arg) =>
    (arg -> forallArg -> ExceptT err u v) ->
    CegisProblem bool u symbolSet model 'True 'True arg 'False () 'True forallArg 'False 'True err v
  CWithForallSpec ::
    (GenSym bool forallSpec forallArg, Evaluate model forallArg) =>
    forallSpec ->
    CegisProblem bool u symbolSet model unResolvedArg haveArg arg 'False () 'True forallArg haveForallIn translate err v ->
    CegisProblem bool u symbolSet model unResolvedArg haveArg arg 'False () 'False forallArg haveForallIn translate err v
  CWithForallIn ::
    (ExtractSymbolics symbolSet forallIn, Evaluate model forallIn) =>
    forallIn ->
    CegisProblem bool u symbolSet model unResolvedArg haveArg arg 'True () 'False () 'True translate err v ->
    CegisProblem bool u symbolSet model unResolvedArg haveArg arg 'False forallIn 'False () 'True translate err v
  CWithArgSpec ::
    (GenSym bool argSpec arg, Evaluate model arg) =>
    argSpec ->
    CegisProblem
      bool
      u
      symbolSet
      model
      'True
      'True
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      haveForallIn
      translate
      err
      v ->
    CegisProblem
      bool
      u
      symbolSet
      model
      'False
      'True
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      haveForallIn
      translate
      err
      v
  CWithTranslate ::
    (CegisTranslation spec bool u err v, Mergeable bool v, Mergeable bool err) =>
    spec ->
    CegisProblem
      bool
      u
      symbolSet
      model
      unResolvedArg
      haveArg
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      haveForallIn
      'True
      err
      v ->
    CegisProblem
      bool
      u
      symbolSet
      model
      unResolvedArg
      haveArg
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      haveForallIn
      'False
      err
      v

sortCegisProblem ::
  CegisProblem
    bool
    u
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
    haveForallIn
    translate
    err
    v ->
  CegisProblem
    bool
    u
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
    haveForallIn
    translate
    err
    v
sortCegisProblem (CWithTranslate spec v) = sortCegisProblem1 $ CWithTranslate spec $ sortCegisProblem v
sortCegisProblem (CWithForallIn fi v) = sortCegisProblem1 $ CWithForallIn fi $ sortCegisProblem v
sortCegisProblem (CWithArgSpec argSpec v) = sortCegisProblem1 $ CWithArgSpec argSpec $ sortCegisProblem v
sortCegisProblem (CWithForallSpec forallSpec v) = sortCegisProblem1 $ CWithForallSpec forallSpec $ sortCegisProblem v
sortCegisProblem v = v

sortCegisProblem1 ::
  CegisProblem
    bool
    u
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
    haveForallIn
    translate
    err
    v ->
  CegisProblem
    bool
    u
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
    haveForallIn
    translate
    err
    v
sortCegisProblem1 (CWithTranslate spec (CWithForallSpec forallSpec v)) =
  CWithForallSpec forallSpec $ sortCegisProblem1 $ CWithTranslate spec v
sortCegisProblem1 (CWithTranslate spec (CWithForallIn fi v)) =
  CWithForallIn fi $ sortCegisProblem1 $ CWithTranslate spec v
sortCegisProblem1 (CWithTranslate spec (CWithArgSpec argSpec v)) =
  CWithArgSpec argSpec $ sortCegisProblem1 $ CWithTranslate spec v
sortCegisProblem1 (CWithForallIn fi (CWithArgSpec argSpec v)) =
  CWithArgSpec argSpec $ sortCegisProblem1 $ CWithForallIn fi v
sortCegisProblem1 (CWithForallSpec forallSpec (CWithArgSpec argSpec v)) =
  CWithArgSpec argSpec $ sortCegisProblem1 $ CWithForallSpec forallSpec v
sortCegisProblem1 v = v

type family CegisResult failure model arg haveArg forallIn forallArg haveForallIn where
  CegisResult failure model arg 'True forallIn forallArg 'True = IO (Either failure (arg, [forallIn], model))
  CegisResult failure model arg 'True forallIn forallArg 'False = IO (Either failure (arg, [forallArg], model))
  CegisResult failure model arg 'False forallIn forallArg 'True = IO (Either failure ([forallIn], model))
  CegisResult failure model arg 'False forallIn forallArg 'False = IO (Either failure ([forallArg], model))

{-
type family ArgByResolved unResolvedArg where
  ArgByResolved 'True = "You have unresolved argBy"
  ArgByResolved 'False = ""

type family ForallInResolved unResolvedForallIn where
  ForallInResolved 'True = "You have unresolved forallIn clause"
  ForallInResolved 'False = ""

type family ForallByResolved unResolvedForallSpec where
  ForallByResolved 'True = "You have unresolved forallBy clause"
  ForallByResolved 'False = ""

type family TranslateByResolved translate where
  TranslateByResolved 'True = "You have unresolved translateBy clause"
  TranslateByResolved 'False = ""

cegis ::
  forall config bool symbolSet failure model unResolvedArg haveArg arg unResolvedForallIn forallIn unResolvedForallArg forallArg translate err v.
  ( ArgByResolved unResolvedArg ~ "",
    ForallByResolved unResolvedForallArg ~ "",
    ForallInResolved unResolvedForallIn ~ "",
    TranslateByResolved translate ~ "",
    Solver config bool symbolSet failure model
  ) =>
  config ->
  CegisProblem bool symbolSet model unResolvedArg haveArg arg unResolvedForallIn forallIn unResolvedForallArg forallArg translate err v ->
  CegisResult failure model arg haveArg
cegis config p = cegisR config (unsafeCoerce p)
-}

cegis ::
  forall config bool u symbolSet failure model haveArg arg forallIn forallArg haveForallIn err v.
  ( UnionSolver config bool u symbolSet failure model
  ) =>
  config ->
  CegisProblem bool u symbolSet model 'False haveArg arg 'False forallIn 'False forallArg haveForallIn 'False err v ->
  CegisResult failure model arg haveArg forallIn forallArg haveForallIn
cegis config v = cegis' $ sortCegisProblem v
  where
    cegis' (CWithForallIn fi (CFormulaPair assumptions assertions)) =
      cegisFormulas config fi assumptions assertions
    cegis' (CWithForallIn fi (CWithTranslate spec (CWithExcept e))) =
      cegisWithExcept spec config fi e
    cegis' (CWithArgSpec argSpec (CWithForallIn fi (CArgFormulaPair formulas))) =
      cegisArgFormulas config fi argSpec formulas
    cegis' (CWithArgSpec argSpec (CWithForallIn fi (CWithTranslate spec (CArgWithExcept e)))) =
      cegisArgWithExcept spec config fi argSpec e
    cegis' (CWithForallSpec forallSpec (CForallFormulaPair formulas)) =
      cegisForallByFormulas config forallSpec formulas
    cegis' (CWithForallSpec forallSpec (CWithTranslate spec (CForallWithExcept e))) =
      cegisForallByWithExcept spec config forallSpec e
    cegis' (CWithArgSpec argSpec (CWithForallSpec forallSpec (CArgForallFormulaPair formulas))) =
      cegisArgForallByFormulas config forallSpec argSpec formulas
    cegis' (CWithArgSpec argSpec (CWithForallSpec forallSpec (CWithTranslate spec (CArgForallWithExcept e)))) =
      cegisArgForallByWithExcept spec config forallSpec argSpec e
    cegis' _ = error "Should not happen"

forallIn ::
  (ExtractSymbolics symbolSet forallIn, Evaluate model forallIn) =>
  forallIn ->
  CegisProblem
    bool
    u
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    'True
    ()
    'False
    ()
    'True
    translate
    err
    v ->
  CegisProblem
    bool
    u
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    'False
    forallIn
    'False
    ()
    'True
    translate
    err
    v
forallIn = CWithForallIn

class ArgByClause argspec input out | input -> out where
  argBy :: argspec -> input -> out

instance
  (GenSym bool argSpec arg, Evaluate model arg) =>
  ArgByClause
    argSpec
    ( CegisProblem
        bool
        u
        symbolSet
        model
        'True
        'True
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        haveForallIn
        translate
        err
        v
    )
    ( CegisProblem
        bool
        u
        symbolSet
        model
        'False
        'True
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        haveForallIn
        translate
        err
        v
    )
  where
  argBy = CWithArgSpec

instance
  (GenSym bool argSpec argType, Evaluate model argType, ExtractSymbolics symbolSet argType) =>
  ArgByClause
    argSpec
    (SolveProblem bool symbolSet model 'True 'True argType translate err v)
    (SolveProblem bool symbolSet model 'False 'True argType translate err v)
  where
  argBy = WithArgSpec

forallBy ::
  (GenSym bool forallSpec forallArg, Evaluate model forallArg) =>
  forallSpec ->
  CegisProblem bool u symbolSet model unResolvedArg haveArg arg 'False () 'True forallArg haveForallIn translate err v ->
  CegisProblem bool u symbolSet model unResolvedArg haveArg arg 'False () 'False forallArg haveForallIn translate err v
forallBy = CWithForallSpec

class TranslateByClause spec input out | input -> out where
  translateBy :: spec -> input -> out

instance
  (SolverTranslation spec bool err v) =>
  TranslateByClause
    spec
    (SolveProblem bool symbolSet model unResolvedArg haveArg argType 'True err v)
    (SolveProblem bool symbolSet model unResolvedArg haveArg argType 'False err v)
  where
  translateBy = WithTranslate

instance
  (CegisTranslation spec bool u err v, Mergeable bool v, Mergeable bool err) =>
  TranslateByClause
    spec
    ( CegisProblem
        bool
        u
        symbolSet
        model
        unResolvedArg
        haveArg
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        haveForallIn
        'True
        err
        v
    )
    ( CegisProblem
        bool
        u
        symbolSet
        model
        unResolvedArg
        haveArg
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        haveForallIn
        'False
        err
        v
    )
  where
  translateBy = CWithTranslate

-}