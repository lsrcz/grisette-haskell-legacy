module Main where

import Control.Monad.Except
import Data.BitVector.Sized.Signed as BVS
import Data.BitVector.Sized.Unsigned as BVU
import GHC.Generics
import Grisette.Backend.SBV
import Grisette.Core
import Grisette.SymPrim.Term

-- Symbolic primitives
symbBool :: Sym Bool
symbBool = ssymb "a"

-- Indexed names
isymbBool :: Sym Bool
isymbBool = isymb 0 "a"

-- Symbolic primitives can hold concrete values for partial evaluation
concBool :: Sym Bool
concBool = conc True

-- Symbolic integers
symbInteger :: Sym Integer
symbInteger = ssymb "b"

-- Symbolic integers with concrete value. You don't have to use 1 here because Sym Integer has a Num instance
concInteger :: Sym Integer
concInteger = 1

-- Symbolic Signed BitVector
symbSignedBV :: Sym (SignedBV 4)
symbSignedBV = ssymb "a"

concSignedBV :: Sym (SignedBV 4)
concSignedBV = 3

concSignedBV' :: Sym (SignedBV 4)
concSignedBV' = 9

concSignedBVCmpWith0' :: Sym Bool
concSignedBVCmpWith0' = concSignedBV' <~ 0

-- Symbolic Unsigned BitVector
symbUnsignedBV :: Sym (UnsignedBV 4)
symbUnsignedBV = ssymb "a"

concUnsignedBV :: Sym (UnsignedBV 4)
concUnsignedBV = 3

concUnsignedBV' :: Sym (UnsignedBV 4)
concUnsignedBV' = 9

concUnsignedBVCmpWith0' :: Sym Bool
concUnsignedBVCmpWith0' = concUnsignedBV' <~ 0

-- Basic operations
-- Symbolic equivalence (SEq type class)
concEq :: Bool -- The result type is Bool, you cannot encode the symbolic equivalence with it
concEq = (ssymb "a" :: Sym Integer) == ssymb "b"

symbEq :: Sym Bool
symbEq = (ssymb "a" :: Sym Integer) ==~ ssymb "b"

symbNeq :: Sym Bool
symbNeq = (ssymb "a" :: Sym Integer) /=~ ssymb "b"

symbEqPartialEval :: Sym Bool
symbEqPartialEval = (ssymb "a" :: Sym Integer) ==~ ssymb "a"

-- Symbolic ordering (SOrd type class)
symbLt :: Sym Bool
symbLt = (ssymb "a" :: Sym Integer) <=~ ssymb "b"

-- Symbolic number-like types (Haskell's standard Num type class)
symbAdd :: Sym Integer
symbAdd = ssymb "a" + ssymb "b"

-- Symbolic composite data type
-- The UnionM monad
-- type UnionM = UnionMBase SymBool
-- Symbolic lists

symbList1 :: UnionM [Sym Bool]
symbList1 = mrgSingle []

symbList2 :: UnionM [Sym Bool]
symbList2 = mrgSingle [ssymb "x"]

symbList3 :: UnionM [Sym Bool]
symbList3 = mrgSingle [ssymb "y"]

symbList4 :: UnionM [Sym Bool]
symbList4 = mrgGuard (ssymb "a") symbList1 symbList3

symbList5 :: UnionM [Sym Bool]
symbList5 = mrgGuard (ssymb "a") symbList2 symbList3

-- UnionM can propagate path conditions correctly
isEmpty :: [Sym Bool] -> Sym Bool
isEmpty [] = conc True
isEmpty _ = conc False

-- This program can be understood as
-- symbList4 = if (a) [] [y]
-- return (isEmpty symbList4)
testIsEmpty :: Sym Bool
testIsEmpty = getSingle $ do
  l <- symbList4
  return $ isEmpty l

-- Working with Errors + show that path conditions are maintained correctly
-- link to the z3 example
getitem :: (Mergeable SymBool a) => SymInteger -> [a] -> ExceptT AssertionError UnionM a
getitem _ [] = throwError AssertionError
getitem i (x : xs) = mrgGuard (i ==~ 0) (mrgReturn x) (getitem (i - 1) xs)

list :: [SymBool]
list = [ssymb "a", ssymb "b"]

correctResult :: ExceptT AssertionError UnionM SymBool
correctResult = mrgGuard (ssymb "c") (getitem (ssymb "d") list) (getitem 1 list)

-- Working with user-defined types
data ConcExpr
  = ConcConst Integer
  | ConcAdd ConcExpr ConcExpr
  | ConcSub ConcExpr ConcExpr
  | ConcEqv ConcExpr ConcExpr
  deriving (Show, Eq, Generic, ToCon Expr)

data Expr
  = Const SymInteger
  | Add (UnionM Expr) (UnionM Expr)
  | Sub (UnionM Expr) (UnionM Expr)
  | Eqv (UnionM Expr) (UnionM Expr)
  deriving (Show, Eq, Generic)
  deriving anyclass (Mergeable SymBool, SEq SymBool, SymEval Model, ToSym ConcExpr)

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
  mrgGuard
    (ssymb "cond")
    (mrgSingle (Const (ssymb "a")))
    (mrgSingle (Add (mrgSingle (Const (ssymb "b"))) (mrgSingle (Const (ssymb "c")))))

mergedSymbExpr2 :: UnionM Expr
mergedSymbExpr2 =
  mrgGuard
    (ssymb "cond1")
    (mrgSingle (Const (ssymb "a1")))
    (mrgSingle (Const (ssymb "a2")))

mergedSymbExpr3 :: UnionM Expr
mergedSymbExpr3 =
  mrgGuard
    (ssymb "cond1")
    (mrgSingle (Add (mrgSingle (Const (ssymb "b1"))) (mrgSingle (Const (ssymb "c1")))))
    (mrgSingle (Add (mrgSingle (Const (ssymb "b2"))) (mrgSingle (Const (ssymb "c2")))))

-- SymEval will be discussed later

-- Maually constructing the sym exprs are laborious and error-prone, how to build them given some specification?
-- The SymGen type class
-- This type class need to be manually written as we cannot guess the user intent
-- We do have some derivation rules for some specific spec types. But they are very restricted.

-- type SymGenState = (Int, String) -- current index + name

-- class (SymBoolOp bool, Mergeable bool a) => SymGen bool spec a where
--   genSymIndexed :: (MonadState SymGenState m) => spec -> m (UnionMBase bool a)

-- Some predefined specs
-- generating a list for symbolic boolean with length in 0-2
symGenList :: UnionM [SymBool]
symGenList = genSym (ListSpec {genListMinLength = 0, genListMaxLength = 2, genListSubSpec = ()}) "a"

-- recursively generate Exprs given a depth
instance SymGen SymBool Integer Expr where
  genSymIndexed i =
    if i <= 0
      then do
        f <- genSymSimpleIndexed @SymBool ()
        return $ mrgSingle $ Const f
      else do
        f <- genSymSimpleIndexed @SymBool ()
        l <- genSymSimpleIndexed @SymBool (i - 1)
        r <- genSymSimpleIndexed @SymBool (i - 1)
        choose (Const f) [Add l r, Sub l r, Eqv l r]

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
instance SymGen SymBool () (UnionM Expr -> UnionM Expr -> UnionM Expr)

instance SymGenSimple SymBool () (UnionM Expr -> UnionM Expr -> UnionM Expr) where
  genSymSimpleIndexed _ =
    let ops = (\op x y -> mrgSingle $ op x y) <$> [Add, Sub, Eqv]
     in simpleChoose @SymBool (head ops) (tail ops)

sketch3 :: UnionM Expr
sketch3 =
  runSymGenIndexed
    ( do
        op <- genSymSimpleIndexed @SymBool ()
        l :: UnionM Expr <- genSymIndexed @SymBool (0 :: Integer)
        r :: UnionM Expr <- genSymIndexed @SymBool (0 :: Integer)
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
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool)

-- The interpretation result type
data Value
  = VB SymBool
  | VI SymInteger
  deriving (Eq, Show, Generic, Mergeable SymBool, SEq SymBool)

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
    (VI x, VI y) -> mrgReturn $ VI $ x + y
    _ -> throwError InvalidProgram
interpretExpr (Sub l r) = interpretBop l r $
  curry $ \case
    (VI x, VI y) -> mrgReturn $ VI $ x - y
    _ -> throwError InvalidProgram
interpretExpr (Eqv l r) = interpretBop l r $
  curry $ \case
    (VI x, VI y) -> mrgReturn $ VB $ x ==~ y
    (VB x, VB y) -> mrgReturn $ VB $ x ==~ y
    _ -> throwError InvalidProgram

-- The user can translate the errors with SolverTranslation type class
-- In this example, there is only one error type.
newtype RefResult = RefResult Integer

instance SolverTranslation RefResult Errors Value where
  errorTranslation _ _ = False
  valueTranslation (RefResult x) v = VI (conc x) ==~ v

-- The sketch is
-- 1 ??op 2
sketch4 :: UnionM Expr
sketch4 =
  runSymGenIndexed
    ( do
        op <- genSymSimpleIndexed @SymBool ()
        return $
          op
            (mrgSingle $ Const $ conc 1 :: UnionM Expr)
            (mrgSingle $ Const $ conc 2 :: UnionM Expr)
    )
    "a"

-- Calling the solver with translation rule.
-- The result has the type: Either CheckSatResult Model.
result :: Integer -> IO ()
result i = do
  m <- solveWithTranslation (RefResult i) (UnboundedReasoning z3) $ interpretExprU sketch4
  case m of
    Left _ -> print "No such expression"
    Right mo -> print (toCon $ symeval True mo sketch4 :: Maybe ConcExpr)

-- True means that for all values that are not mentioned in the model, we should fill in a default value.
-- This is possible because the partial evaluator may strip some variables

-- Construcing the sketch is still so hard? We can write a parser for a sketch like language and
-- directly construct the symbolic program with it.
--
--   genSymIndexed :: (MonadState SymGenState m) => spec -> m (UnionMBase bool a)
--                    ^^^^^^^^^^^^^^^^^^^^^^^^^^
-- You can add a state monad to your parser monad stack, and you can generate symbolic programs with it

-- Stateful computation? Just another stack of monad, and nothing surprising.

main :: IO ()
main = putStrLn "Hello world"
