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

module Grisette.Data.Class.Solver
  ( SolverErrorTranslation (..),
    SolverTranslation (..),
    CegisErrorTranslation (..),
    CegisTranslation (..),
    Solver (..),
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
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Data.Hashable
import Generics.Deriving
import Grisette.Control.Exception
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Evaluate
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.GenSym
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.UnionOp
import Language.Haskell.TH.Syntax

class SolverErrorTranslation spec e | spec -> e where
  errorTranslation :: spec -> e -> Bool

class (SymBoolOp bool, SolverErrorTranslation spec e) => SolverTranslation spec bool e v | spec bool -> e v where
  valueTranslation :: spec -> v -> bool

class CegisErrorTranslation spec e | spec -> e where
  cegisErrorTranslation :: spec -> e -> VerificationConditions

class (SymBoolOp bool, CegisErrorTranslation spec e) => CegisTranslation spec bool e v | spec bool -> e v where
  cegisValueTranslation :: spec -> v -> ExceptT VerificationConditions (UnionMBase bool) ()
  default cegisValueTranslation :: (v ~ ()) => spec -> v -> ExceptT VerificationConditions (UnionMBase bool) ()
  cegisValueTranslation _ = mrgReturn

translateExceptT :: (SolverTranslation spec bool e v) => spec -> ExceptT e (UnionMBase bool) v -> bool
translateExceptT p (ExceptT u) =
  getSingle $
    ( \case
        Left e -> conc $ errorTranslation p e
        Right v -> valueTranslation p v
    )
      <$> u

translateCegis :: forall spec bool e v. (CegisTranslation spec bool e v) => spec -> ExceptT e (UnionMBase bool) v -> (bool, bool)
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
              (runExceptT $ cegisValueTranslation p v :: UnionMBase bool (Either VerificationConditions ()))
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
  cegisFormulas :: (ExtractSymbolics symbolSet forallArg) => config -> forallArg -> bool -> bool -> IO (Either failure model)

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
  solveWithExcept ::
    (SolverTranslation spec bool err v) =>
    spec ->
    config ->
    ExceptT err (UnionMBase bool) v ->
    IO (Either failure model)
  solveWithExcept spec config e = solveFormula config (translateExceptT spec e)
  solveArgWithExcept ::
    forall spec arg argSpec err v.
    ( SolverTranslation spec bool err v,
      GenSym bool argSpec arg,
      Evaluate model arg,
      ExtractSymbolics symbolSet arg
    ) =>
    spec ->
    config ->
    argSpec ->
    (arg -> ExceptT err (UnionMBase bool) v) ->
    IO (Either failure (arg, model))
  solveArgWithExcept spec config argSpec f = solveArgFormula config argSpec (translateExceptT spec . f)
  solveWithExceptMulti ::
    (SolverTranslation spec bool err v) =>
    spec ->
    config ->
    Int ->
    ExceptT err (UnionMBase bool) v ->
    IO [model]
  solveWithExceptMulti spec config n e = solveFormulaMulti config n (translateExceptT spec e)
  cegisWithExcept ::
    (CegisTranslation spec bool err v, ExtractSymbolics symbolSet forallArgs) =>
    spec ->
    config ->
    forallArgs ->
    ExceptT err (UnionMBase bool) v ->
    IO (Either failure model)
  cegisWithExcept p config foralls e =
    let (assumes, asserts) = translateCegis p e
     in cegisFormulas config foralls assumes asserts
  cegisForallByWithExcept ::
    forall err spec forallSpec a v.
    ( CegisTranslation spec bool err v,
      ExtractSymbolics symbolSet a,
      ExtractSymbolics symbolSet bool,
      GenSym bool forallSpec a,
      Mergeable bool err,
      Mergeable bool v
    ) =>
    spec ->
    config ->
    forallSpec ->
    (a -> ExceptT err (UnionMBase bool) v) ->
    IO (Either failure model)
  cegisForallByWithExcept p config forallSpec f =
    let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool a
     in cegisWithExcept p config forallArgs (f #~ forallArgs)
  cegisForallByFormulas ::
    forall spec a.
    (ExtractSymbolics symbolSet a, ExtractSymbolics symbolSet bool, GenSym bool spec a) =>
    config ->
    spec ->
    (a -> (bool, bool)) ->
    IO (Either failure model)
  cegisForallByFormulas config forallSpec formulas =
    let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool a
     in uncurry (cegisFormulas config forallArgs) (formulas #~ forallArgs)

  cegisArgWithExcept ::
    forall spec err v forallArgs argSpec arg.
    ( CegisTranslation spec bool err v,
      ExtractSymbolics symbolSet forallArgs,
      GenSym bool argSpec arg,
      Mergeable bool v,
      Mergeable bool err,
      Evaluate model arg
    ) =>
    spec ->
    config ->
    forallArgs ->
    argSpec ->
    (arg -> ExceptT err (UnionMBase bool) v) ->
    IO (Either failure (arg, model))
  cegisArgWithExcept p config foralls argSpec f =
    let args = genSym argSpec (nameWithInfo "arg" SolveInternal) :: UnionMBase bool arg
        (assumes, asserts) = translateCegis p (f #~ args) :: (bool, bool)
     in do
          r <- cegisFormulas config foralls assumes asserts
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
  cegisArgForallByWithExcept ::
    forall err spec forallSpec forallArg argSpec arg v.
    ( CegisTranslation spec bool err v,
      ExtractSymbolics symbolSet forallArg,
      ExtractSymbolics symbolSet bool,
      GenSym bool forallSpec forallArg,
      GenSym bool argSpec arg,
      Mergeable bool err,
      Mergeable bool v,
      Evaluate model arg
    ) =>
    spec ->
    config ->
    forallSpec ->
    argSpec ->
    (arg -> forallArg -> ExceptT err (UnionMBase bool) v) ->
    IO (Either failure (arg, model))
  cegisArgForallByWithExcept p config forallSpec argSpec f =
    let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool forallArg
     in cegisArgWithExcept p config forallArgs argSpec (flip f #~ forallArgs)
  cegisArgFormulas ::
    forall forallArg argSpec arg.
    (ExtractSymbolics symbolSet forallArg, GenSym bool argSpec arg, Evaluate model arg) =>
    config ->
    forallArg ->
    argSpec ->
    (arg -> (bool, bool)) ->
    IO (Either failure (arg, model))
  cegisArgFormulas config forallArg argSpec formulas =
    let args = genSym argSpec (nameWithInfo "arg" SolveInternal) :: UnionMBase bool arg
     in do
          r <- uncurry (cegisFormulas config forallArg) (formulas #~ args)
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
  cegisArgForallByFormulas ::
    forall forallSpec forallArg argSpec arg.
    ( ExtractSymbolics symbolSet forallArg,
      ExtractSymbolics symbolSet bool,
      GenSym bool forallSpec forallArg,
      GenSym bool argSpec arg,
      Evaluate model arg
    ) =>
    config ->
    forallSpec ->
    argSpec ->
    (arg -> forallArg -> (bool, bool)) ->
    IO (Either failure (arg, model))
  cegisArgForallByFormulas config forallSpec argSpec formulas =
    let forallArgs = genSym forallSpec (nameWithInfo "forallarg" SolveInternal) :: UnionMBase bool forallArg
     in cegisArgFormulas config forallArgs argSpec (flip formulas #~ forallArgs)

data
  SolveProblem
    bool
    symbolSet
    model
    (unResolvedArg :: Bool)
    (haveArg :: Bool)
    (argType :: *)
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
    symbolSet
    model
    (unResolvedArg :: Bool)
    (haveArg :: Bool)
    arg
    (unResolvedForallIn :: Bool)
    forallIn
    (unResolvedForallArg :: Bool)
    forallArg
    (translate :: Bool)
    err
    v
  where
  CFormulaPair :: bool -> bool -> CegisProblem bool symbolSet model 'False 'False () 'True () 'False () 'False () ()
  CWithExcept ::
    ExceptT err (UnionMBase bool) v ->
    CegisProblem bool symbolSet model 'False 'False () 'True () 'False () 'True err v
  CArgFormulaPair ::
    (arg -> (bool, bool)) ->
    CegisProblem bool symbolSet model 'True 'True arg 'True () 'False () 'False () ()
  CForallFormulaPair ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg) =>
    (forallArg -> (bool, bool)) ->
    CegisProblem bool symbolSet model 'False 'False () 'False () 'True forallArg 'False () ()
  CArgForallFormulaPair ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg) =>
    (arg -> forallArg -> (bool, bool)) ->
    CegisProblem bool symbolSet model 'True 'True arg 'False () 'True forallArg 'False () ()
  CArgWithExcept ::
    (arg -> ExceptT err (UnionMBase bool) v) ->
    CegisProblem bool symbolSet model 'True 'True arg 'True () 'False () 'True err v
  CForallWithExcept ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg) =>
    (forallArg -> ExceptT err (UnionMBase bool) v) ->
    CegisProblem bool symbolSet model 'False 'False () 'False () 'True forallArg 'True err v
  CArgForallWithExcept ::
    (ExtractSymbolics symbolSet bool, ExtractSymbolics symbolSet forallArg, ExtractSymbolics symbolSet arg) =>
    (arg -> forallArg -> ExceptT err (UnionMBase bool) v) ->
    CegisProblem bool symbolSet model 'True 'True arg 'False () 'True forallArg 'True err v
  CWithForallSpec ::
    (GenSym bool forallSpec forallArg) =>
    forallSpec ->
    CegisProblem bool symbolSet model unResolvedArg haveArg arg 'False () 'True forallArg translate err v ->
    CegisProblem bool symbolSet model unResolvedArg haveArg arg 'False () 'False forallArg translate err v
  CWithForallIn ::
    (ExtractSymbolics symbolSet forallIn) =>
    forallIn ->
    CegisProblem bool symbolSet model unResolvedArg haveArg arg 'True () 'False () translate err v ->
    CegisProblem bool symbolSet model unResolvedArg haveArg arg 'False forallIn 'False () translate err v
  CWithArgSpec ::
    (GenSym bool argSpec arg, Evaluate model arg) =>
    argSpec ->
    CegisProblem
      bool
      symbolSet
      model
      'True
      'True
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      translate
      err
      v ->
    CegisProblem
      bool
      symbolSet
      model
      'False
      'True
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      translate
      err
      v
  CWithTranslate ::
    (CegisTranslation spec bool err v, Mergeable bool v, Mergeable bool err) =>
    spec ->
    CegisProblem
      bool
      symbolSet
      model
      unResolvedArg
      haveArg
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      'True
      err
      v ->
    CegisProblem
      bool
      symbolSet
      model
      unResolvedArg
      haveArg
      arg
      unResolvedForallIn
      forallIn
      unResolvedForallArg
      forallArg
      'False
      err
      v

sortCegisProblem ::
  CegisProblem
    bool
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
    translate
    err
    v ->
  CegisProblem
    bool
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
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
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
    translate
    err
    v ->
  CegisProblem
    bool
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    unResolvedForallIn
    forallIn
    unResolvedForallArg
    forallArg
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

type family CegisResult failure model arg haveArg where
  CegisResult failure model arg 'True = IO (Either failure (arg, model))
  CegisResult failure model arg 'False = IO (Either failure model)

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

{-
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
  forall config bool symbolSet failure model haveArg arg forallIn forallArg err v.
  ( Solver config bool symbolSet failure model
  ) =>
  config ->
  CegisProblem bool symbolSet model 'False haveArg arg 'False forallIn 'False forallArg 'False err v ->
  CegisResult failure model arg haveArg
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
  (ExtractSymbolics symbolSet forallIn) =>
  forallIn ->
  CegisProblem
    bool
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    'True
    ()
    'False
    ()
    translate
    err
    v ->
  CegisProblem
    bool
    symbolSet
    model
    unResolvedArg
    haveArg
    arg
    'False
    forallIn
    'False
    ()
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
        symbolSet
        model
        'True
        'True
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        translate
        err
        v
    )
    ( CegisProblem
        bool
        symbolSet
        model
        'False
        'True
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
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
  (GenSym bool forallSpec forallArg) =>
  forallSpec ->
  CegisProblem bool symbolSet model unResolvedArg haveArg arg 'False () 'True forallArg translate err v ->
  CegisProblem bool symbolSet model unResolvedArg haveArg arg 'False () 'False forallArg translate err v
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
  (CegisTranslation spec bool err v, Mergeable bool v, Mergeable bool err) =>
  TranslateByClause
    spec
    ( CegisProblem
        bool
        symbolSet
        model
        unResolvedArg
        haveArg
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        'True
        err
        v
    )
    ( CegisProblem
        bool
        symbolSet
        model
        unResolvedArg
        haveArg
        arg
        unResolvedForallIn
        forallIn
        unResolvedForallArg
        forallArg
        'False
        err
        v
    )
  where
  translateBy = CWithTranslate
