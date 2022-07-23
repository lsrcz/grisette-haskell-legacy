{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Grisette.Tutorial.ComplexExprSynth.ComplexExprSynth
  ( Expr (..),
    SymExpr (..),
    Type (..),
    Error (..),
    Value (..),
    SymValue (..),
    Typer,
    Interpreter,
    binary,
    ternary,
    typer,
    typerBad,
    interpreter,
    VerifyTyper (..),
    verifyTyper,
    SynthExpr (..),
    synthExpr,
    main,
  )
where

import Control.Monad.Except
import GHC.Generics
import Grisette

data Expr
  = BoolConst Bool
  | IntegerConst Integer
  | Add Expr Expr
  | And Expr Expr
  | Eqv Expr Expr
  | ITE Expr Expr Expr
  deriving (Show, Generic)
  deriving (ToCon SymExpr) via (Default Expr)

data SymExpr
  = SymBoolConst SymBool
  | SymIntegerConst SymInteger
  | SymAdd (UnionM SymExpr) (UnionM SymExpr)
  | SymAnd (UnionM SymExpr) (UnionM SymExpr)
  | SymEqv (UnionM SymExpr) (UnionM SymExpr)
  | SymITE (UnionM SymExpr) (UnionM SymExpr) (UnionM SymExpr)
  deriving (Show, Generic)
  deriving (ToSym Expr, Mergeable SymBool, Evaluate Model) via (Default SymExpr)

data Type
  = BoolType
  | IntegerType
  deriving (Show, Generic)
  deriving (Mergeable SymBool) via (Default Type)

data Error
  = TyperError
  | ExecutionError
  deriving (Show, Generic)
  deriving (Mergeable SymBool) via (Default Error)

data Value
  = BoolValue Bool
  | IntegerValue Integer
  deriving (Show, Generic)
  deriving (ToCon SymValue) via (Default Value)

data SymValue
  = SymBoolValue SymBool
  | SymIntegerValue SymInteger
  deriving (Show, Generic)
  deriving (Mergeable SymBool, ToSym Value, SEq SymBool) via (Default SymValue)

$(makeUnionMWrapper "u" ''SymExpr)
$(makeUnionMWrapper "u" ''Type)
$(makeUnionMWrapper "u" ''SymValue)

instance GenSym SymBool Integer SymExpr where
  genSymFresh depth
    | depth <= 0 = do
      b1 <- genSymSimpleFresh ()
      i1 <- genSymSimpleFresh ()
      choose [SymBoolConst b1, SymIntegerConst i1]
    | otherwise = do
      b1 <- genSymSimpleFresh ()
      i1 <- genSymSimpleFresh ()
      v1 <- genSymFresh (depth - 1)
      v2 <- genSymFresh (depth - 1)
      v3 <- genSymFresh (depth - 1)
      choose [SymBoolConst b1, SymIntegerConst i1, SymAdd v1 v2, SymAnd v1 v2, SymEqv v1 v2, SymITE v1 v2 v3]

type Typer = SymExpr -> ExceptT Error UnionM Type

type Interpreter = SymExpr -> ExceptT Error UnionM SymValue

binary ::
  (Mergeable SymBool a) =>
  (SymExpr -> ExceptT Error UnionM a) ->
  UnionM SymExpr ->
  UnionM SymExpr ->
  ((a, a) -> ExceptT Error UnionM a) ->
  ExceptT Error UnionM a
binary f l r comb = do
  lt <- f #~ l
  rt <- f #~ r
  curry comb lt rt

ternary ::
  (Mergeable SymBool a) =>
  (SymExpr -> ExceptT Error UnionM a) ->
  UnionM SymExpr ->
  UnionM SymExpr ->
  UnionM SymExpr ->
  ((a, a, a) -> ExceptT Error UnionM a) ->
  ExceptT Error UnionM a
ternary f c l r comb = do
  ct <- f #~ c
  lt <- f #~ l
  rt <- f #~ r
  comb (ct, lt, rt)

typer :: Typer
typer (SymBoolConst _) = uBoolType
typer (SymIntegerConst _) = uIntegerType
typer (SymAdd l r) = binary typer l r $ \case
  (IntegerType, IntegerType) -> uIntegerType
  _ -> mrgThrowError TyperError
typer (SymAnd l r) = binary typer l r $ \case
  (BoolType, BoolType) -> uBoolType
  _ -> mrgThrowError TyperError
typer (SymEqv l r) = binary typer l r $ \case
  (BoolType, BoolType) -> uBoolType
  (IntegerType, IntegerType) -> uBoolType
  _ -> mrgThrowError TyperError
typer (SymITE c l r) = ternary typer c l r $ \case
  (BoolType, BoolType, BoolType) -> uBoolType
  (BoolType, IntegerType, IntegerType) -> uIntegerType
  _ -> mrgThrowError TyperError

typerBad :: Typer
typerBad (SymBoolConst _) = uBoolType
typerBad (SymIntegerConst _) = uIntegerType
typerBad (SymAdd l r) = binary typerBad l r $ \case
  (IntegerType, IntegerType) -> uIntegerType
  _ -> mrgThrowError TyperError
typerBad (SymAnd l r) = binary typerBad l r $ \case
  (BoolType, BoolType) -> uBoolType
  _ -> mrgThrowError TyperError
typerBad (SymEqv l r) = binary typerBad l r $ \case
  (BoolType, BoolType) -> uBoolType
  -- Bug here
  (IntegerType, IntegerType) -> uIntegerType
  _ -> mrgThrowError TyperError
typerBad (SymITE c l r) = ternary typerBad c l r $ \case
  (BoolType, BoolType, BoolType) -> uBoolType
  (BoolType, IntegerType, IntegerType) -> uIntegerType
  _ -> mrgThrowError TyperError

interpreter :: Interpreter
interpreter (SymBoolConst v) = uSymBoolValue v
interpreter (SymIntegerConst v) = uSymIntegerValue v
interpreter (SymAdd l r) = binary interpreter l r $ \case
  (SymIntegerValue li, SymIntegerValue ri) -> uSymIntegerValue $ li + ri
  _ -> mrgThrowError ExecutionError
interpreter (SymAnd l r) = binary interpreter l r $ \case
  (SymBoolValue lb, SymBoolValue rb) -> uSymBoolValue $ lb &&~ rb
  _ -> mrgThrowError ExecutionError
interpreter (SymEqv l r) = binary interpreter l r $ \case
  (SymBoolValue lb, SymBoolValue rb) -> uSymBoolValue $ lb ==~ rb
  (SymIntegerValue li, SymIntegerValue ri) -> uSymBoolValue $ li ==~ ri
  _ -> mrgThrowError ExecutionError
interpreter (SymITE c l r) = ternary interpreter c l r $ \case
  (SymBoolValue cb, SymBoolValue lb, SymBoolValue rb) -> uSymBoolValue $ ites cb lb rb
  (SymBoolValue cb, SymIntegerValue li, SymIntegerValue ri) -> uSymIntegerValue $ ites cb li ri
  _ -> mrgThrowError ExecutionError

data VerifyTyper = VerifyTyper


instance SolverErrorTranslation VerifyTyper Error where
  errorTranslation _ ExecutionError = True
  errorTranslation _ _ = False

instance SolverTranslation VerifyTyper SymBool Error SymValue where
  valueTranslation _ _ = conc False

verifyTyper :: GrisetteSMTConfig n -> Typer -> Interpreter -> IO (Maybe Expr)
verifyTyper config typerImpl interpreterImpl = do
  let sk :: UnionM SymExpr = genSym (3 :: Integer) $$(nameWithLoc "a")
  let r = (typerImpl #~ sk) >>~ (interpreterImpl #~ sk)
  m <- solveWithExcept VerifyTyper config r
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateToCon mo sk

newtype SynthExpr = SynthExpr Value

instance SolverErrorTranslation SynthExpr Error where
  errorTranslation _ _ = False

instance SolverTranslation SynthExpr SymBool Error SymValue where
  valueTranslation (SynthExpr expect) actual = toSym expect ==~ actual

synthExpr :: GrisetteSMTConfig n -> UnionM SymExpr -> Value -> IO (Maybe Expr)
synthExpr config sketch expect = do
  let r = interpreter #~ sketch
  m <- solveWithExcept (SynthExpr expect) config r
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateToCon mo sketch

main :: IO ()
main = do
  let config = UnboundedReasoning z3
  verifyTyper config typer interpreter >>= print
  verifyTyper config typerBad interpreter >>= print
  synthExpr config (genSym (3 :: Integer) $$(nameWithLoc "a")) (BoolValue True) >>= print
  synthExpr
    config
    (uSymAdd (uSymIntegerConst (ssymb "a")) (uSymIntegerConst (ssymb "b")))
    (BoolValue True)
    >>= print
  synthExpr
    config
    (uSymAdd (uSymIntegerConst (ssymb "a")) (uSymIntegerConst (ssymb "b")))
    (IntegerValue 10)
    >>= print
