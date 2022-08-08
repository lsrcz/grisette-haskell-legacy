{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.Except
import GHC.Generics
import Grisette
import Data.Proxy

-- Symbolic primitives
symbBool :: Sym Bool
symbBool = ssymb "a" -- simple symbolic
-- similar to Rosette's define-symbolic (without *).
-- We can implement something similart to rosette's
-- define-symbolic with template haskell

-- $(define-symbolic a Bool) := a = ssymb "a"

symbBoolOverloadedStr :: Sym Bool
symbBoolOverloadedStr = "a" -- simple symbolic

-- Fresh names
isymbBool :: Sym Bool
isymbBool = isymb "a" 0 -- indexed symbolic "a#0"

-- Symbolic primitives can hold concrete values for partial evaluation
concBool :: Sym Bool
concBool = conc True

-- Symbolic integers
symbInteger :: Sym Integer
symbInteger = "b"

-- Symbolic integers with concrete value.
-- You don't have to use 1 here because Sym Integer has a Num instance
concInteger :: Sym Integer
concInteger = 1

-- Symbolic Signed BitVector
symbIntN :: Sym (IntN 4)
symbIntN = "a"

concIntN :: Sym (IntN 4)
concIntN = 3

concIntN' :: Sym (IntN 4)
concIntN' = 9 -- -7

concIntNCmpWith0' :: Sym Bool
concIntNCmpWith0' = concIntN' <~ 0 -- true <~ SOrd

-- Symbolic Unsigned BitVector
symbWordN :: Sym (WordN 4)
symbWordN = "a"

concWordN :: Sym (WordN 4)
concWordN = 3

concWordN' :: Sym (WordN 4)
concWordN' = 9

concWordNCmpWith0' :: Sym Bool
concWordNCmpWith0' = concWordN' <~ 0

-- bvult bvslt

-- Basic operations
-- Symbolic equivalence (SEq type class)
concEq :: Bool -- The result type is Bool,
-- you cannot encode the symbolic equivalence with it
concEq = ("a" :: Sym Integer) == "b" -- False

symbEq :: Sym Bool
symbEq = ("a" :: Sym Integer) ==~ "b" -- (= a b)

symbNeq :: Sym Bool
symbNeq = ("a" :: Sym Integer) /=~ "b"

symbEqPartialEval :: Sym Bool
symbEqPartialEval = ("a" :: Sym Integer) ==~ "a"

-- Symbolic ordering (SOrd type class)
symbLe :: Sym Bool
symbLe = ("a" :: Sym Integer) <=~ "b"

-- Symbolic number-like types (Haskell's standard Num type class)
symbAdd :: Sym Integer
symbAdd = "a" + "b"

-- Symbolic composite data type
-- The UnionM monad
-- type UnionM = UnionMBase SymBool
-- Symbolic lists

symbList1 :: UnionM [Sym Bool]
symbList1 = mrgReturn []

symbList2 :: UnionM [Sym Bool]
symbList2 = mrgReturn ["x"]

symbList3 :: UnionM [Sym Bool]
symbList3 = mrgReturn ["y"]

symbList4 :: UnionM [Sym Bool]
symbList4 = mrgIf "a" symbList1 symbList3

symbList5 :: UnionM [Sym Bool]
symbList5 = mrgIf "a" symbList2 symbList3

-- UnionM can propagate path conditions correctly
isEmpty :: [Sym Bool] -> Sym Bool
isEmpty [] = conc True
isEmpty _ = conc False

-- This program can be understood as
-- symbList4 = if (a) [] [y]
-- return (isEmpty symbList4)
testIsEmpty :: Sym Bool
testIsEmpty = getSingle $ do
  -- getSingle extracts SymBool from (UnionM (SymBool))
  l <- symbList4
  return $ isEmpty l

-- Working with Errors + show that path conditions are maintained correctly
-- link to the z3 example
getitem :: (Mergeable SymBool a) => SymInteger -> [a] -> ExceptT AssertionError UnionM a
getitem _ [] = throwError AssertionError
getitem i (x : xs) = mrgIf (i ==~ 0) (mrgReturn x) (getitem (i - 1) xs)

-- getitem if i is in range, return list[i], or return AssertionError
list :: [SymBool]
list = ["a", "b"]

correctResult :: ExceptT AssertionError UnionM SymBool
-- UnionM (Either AssertionError SymBool)
correctResult = mrgIf "c" (getitem "d" list) (getitem 1 list)

-- Working with user-defined types
data ConcExpr
  = ConcConst Integer
  | ConcAdd ConcExpr ConcExpr
  | ConcSub ConcExpr ConcExpr
  | ConcEqv ConcExpr ConcExpr
  deriving (Show, Eq, Generic)
  deriving (ToCon Expr) via (Default ConcExpr)

-- a + b - 2 == 10
data Expr
  = Const SymInteger
  | Add (UnionM Expr) (UnionM Expr)
  | Sub (UnionM Expr) (UnionM Expr)
  | Eqv (UnionM Expr) (UnionM Expr)
  deriving (Show, Eq, Generic)
  deriving
    ( Mergeable SymBool,
      Evaluate Model,
      ToSym ConcExpr,
      SEq SymBool
    ) via (Default Expr)

$(makeUnionMWrapper "u" ''Expr)

-- you can write this as deriving (Show, Eq, Generic, Mergeable SymBool ...)

-- What are these type classes?
-- SEq/SOrd are shown before
-- ToCon/ToSym: conversion between symbolic / concrete types

concExpr :: ConcExpr
concExpr = ConcAdd (ConcConst 1) (ConcConst 2)

symbExpr :: Expr
symbExpr = toSym concExpr

-- it's possible that a symbolic value cannot be converted to concrete type, so we need Maybe
concExpr' :: Maybe ConcExpr
concExpr' = toCon symbExpr

-- Mergeable: state merging
mergedSymbExpr1 :: UnionM Expr
mergedSymbExpr1 =
  mrgIf
    "cond"
    (uConst "a")
    (uAdd (uConst "b") (uConst "c"))

mergedSymbExpr2 :: UnionM Expr
mergedSymbExpr2 =
  mrgIf "cond1" (uConst "a1") (uConst "a2")

mergedSymbExpr3 :: UnionM Expr
mergedSymbExpr3 =
  mrgIf "cond1"
    (uAdd (uConst "b1") (uConst "c1"))
    (uAdd (uConst "b2") (uConst "c2"))

-- Evaluate will be discussed later

-- Maually constructing the sym exprs are laborious and error-prone, how to build them given some specification?
-- The GenSym type class
-- This type class need to be manually written as we cannot guess the user intent
-- We do have some derivation rules for some specific spec types. But they are very restricted.

-- type GenSymState = (Int, String) -- current index + name

-- class (SymBoolOp bool, Mergeable bool a) => GenSym bool spec a where
--   genSymFresh :: (MonadState GenSymState m) => spec -> m (UnionMBase bool a)

-- Some predefined specs
-- generating a list for symbolic boolean with length in 0-2
symGenList :: UnionM [SymBool]
symGenList = genSym (ListSpec {genListMinLength = 0, genListMaxLength = 2, genListSubSpec = ()}) "a"

-- recursively generate Exprs given a depth
instance GenSym SymBool Integer Expr where
  genSymFresh i =
    if i <= 0
      then do
        f <- genSymSimpleFresh ()
        return $ uConst f
      else -- You still need to write this mrgReturn.
      -- I realized that forcing the user to insert mrgReturn/mrgReturn everywhere is not a good idea
      -- probably in the future we can automatically generate functions like
      -- singleConst = mrgReturn . Const with Template Haskell

      -- In scala we can use implicit conversions.
      -- No need for metaprogramming
      do
        f <- genSymSimpleFresh ()
        l <- genSymSimpleFresh (i - 1)
        r <- genSymSimpleFresh (i - 1)
        choose [Const f, Add l r, Sub l r, Eqv l r]

sketch1 :: UnionM Expr
sketch1 = genSym (1 :: Integer) "a"

sketch2 :: UnionM Expr
sketch2 = genSym (2 :: Integer) "b"

-- generate an operator
-- this would be useful if you want to build a sketch-like language
-- e.g.
-- if (a ?? b < 2) {
-- }
-- here ?? is an operator
instance GenSym SymBool () (UnionM Expr -> UnionM Expr -> UnionM Expr)

instance GenSymSimple () (UnionM Expr -> UnionM Expr -> UnionM Expr) where
  genSymSimpleFresh _ = simpleChoose (Proxy :: Proxy SymBool) [uAdd, uSub, uEqv]

sketch3 :: UnionM Expr
sketch3 =
  runGenSymFresh
    ( do
        op <- genSymSimpleFresh ()
        l :: UnionM Expr <- genSymFresh (0 :: Integer)
        r :: UnionM Expr <- genSymFresh (0 :: Integer)
        return $ op l r
    )
    "a"

-- Let's write the interpreter, we will first define the possible errors
-- In Grisette, the errors are not hard coded.
-- The library provided the following two standard error types for traditional verifications,
-- but you can define your own ones
--
-- data AssertionError = AssertionError
--
-- data VerificationConditions
--  = AssertionViolation
--  | AssumptionViolation
data Errors
  = InvalidProgram
  deriving (Show, Eq, Generic)
  deriving (SEq SymBool, Mergeable SymBool) via (Default Errors)

-- The interpretation result type
data Value
  = VB SymBool
  | VI SymInteger
  deriving (Eq, Show, Generic)
  deriving (SEq SymBool, Mergeable SymBool) via (Default Value)

$(makeUnionMWrapper "u" ''Value)

-- A monadic interpreter. Nothing special
interpretBop ::
  UnionM Expr ->
  UnionM Expr ->
  (Value -> Value -> ExceptT Errors UnionM Value) ->
  ExceptT Errors UnionM Value
interpretBop l r f = do
  lv <- interpretExprU l
  rv <- interpretExprU r
  f lv rv

interpretExprU :: UnionM Expr -> ExceptT Errors UnionM Value
interpretExprU x = lift x >>= interpretExpr

interpretExpr :: Expr -> ExceptT Errors UnionM Value
interpretExpr (Const i) = mrgReturn $ VI i
interpretExpr (Add l r) = interpretBop l r $
  curry $ \case
    (VI x, VI y) -> uVI $ x + y -- a lot of mrgReturns
    _ -> throwError InvalidProgram
interpretExpr (Sub l r) = interpretBop l r $
  curry $ \case
    (VI x, VI y) -> uVI $ x - y
    _ -> throwError InvalidProgram
interpretExpr (Eqv l r) = interpretBop l r $
  curry $ \case
    (VI x, VI y) -> uVB $ x ==~ y -- mrgReturn
    (VB x, VB y) -> uVB $ x ==~ y
    _ -> throwError InvalidProgram

-- The user can translate the errors with SolverTranslation type class
-- In this example, there is only one error type.
newtype RefResult = RefResult Integer


instance ToAssertion RefResult SymBool (Either Errors Value) where
  toAssertion (RefResult x) (Right v) = VI (conc x) ==~ v
  toAssertion _ _ = conc False

-- The sketch is
-- 1 ??op 2
sketch4 :: UnionM Expr
sketch4 =
  runGenSymFresh
    ( do
        op <- genSymSimpleFresh ()
        return $ op (uConst 1 :: UnionM Expr) (uConst 2 :: UnionM Expr)
    )
    "a"

-- Calling the solver with translation rule.
-- The result has the type: Either CheckSatResult Model.
result :: Integer -> IO ()
result i = do
  m <- solve (RefResult i) (UnboundedReasoning z3) $ runExceptT $ interpretExprU sketch4
  case m of
    Left _ -> putStrLn "No such expression"
    Right mo -> print (toCon $ evaluate True mo sketch4 :: Maybe ConcExpr)

-- True means that for all values that are not mentioned in the model, we should fill in a default value.
-- This is possible because the partial evaluator may strip some variables

-- Construcing the sketch is still so hard? We can write a parser for a sketch like language and
-- directly construct the symbolic program with it.
--
--   genSymFresh :: (MonadState GenSymState m) => spec -> m (UnionMBase bool a)
--                    ^^^^^^^^^^^^^^^^^^^^^^^^^^
-- You can add a state monad to your parser monad stack, and you can generate symbolic programs with it

-- Stateful computation? Just another stack of monad, and nothing surprising.

main :: IO ()
main = putStrLn "Hello world"
