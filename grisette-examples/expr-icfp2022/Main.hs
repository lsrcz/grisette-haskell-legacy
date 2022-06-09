{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad.Except
import GHC.Generics
import Grisette
import Data.Maybe

-- The concrete AST definition.
-- This is only used for printing purpose as printing the
-- symbolic type would give us quite a lot 'UMrg' / 'Single',
-- and the result would be hard to read.
data Expr = Lit LitExpr | Ops OpsExpr
  deriving (Show, Generic)
  deriving
    ( ToCon SExpr -- ToCon converts a SExpr to Maybe Expr.
    )
    via (Default Expr)

data LitExpr = BoolLit Bool | ListLit [Bool]
  deriving (Show, Generic)
  deriving (ToCon SLitExpr) via (Default LitExpr)

data OpsExpr
  = -- Head []          -->   RuntimeError
    -- Head (x:xs)      -->   x
    -- Head _           -->   TypeError
    HeadExpr Expr
  | -- And boolx booly  -->   boolx && booly
    -- And _ _          -->   TypeError
    AndExpr Expr Expr
  | -- Cons boolx listy -->   boolx : listy
    -- Cons _ _         -->   TypeError
    ConsExpr Expr Expr
  | -- Tail []          -->   RuntimeError
    -- Tail (x:xs)      -->   xs
    -- Tail _           -->   TypeError
    TailExpr Expr
  | -- Or boolx booly   -->   boolx || booly
    -- Or _ _           -->   TypeError
    OrExpr Expr Expr
  | -- Not boolx        -->   not boolx
    -- Not _            -->   TypeError
    NotExpr Expr
  deriving (Show, Generic)
  deriving (ToCon SOpsExpr) via (Default OpsExpr)

-- The symbolic AST definition
data SExpr = SLit SLitExpr | SOps SOpsExpr
  deriving (Show, Generic)
  deriving
    ( Mergeable SymBool, -- How to merge the values
      ToSym Expr, -- ToSym converts Expr to SExpr
      Evaluate Model -- Evaluates a SExpr with a Model generated by the solver
    )
    via (Default SExpr)

data SLitExpr = SBoolLit SymBool | SListLit (UnionM [SymBool])
  deriving (Show, Generic)
  deriving
    ( Mergeable SymBool,
      ToSym LitExpr,
      SEq SymBool, -- Symbolic equivalence relation, provided ==~ operator
      Evaluate Model
    )
    via (Default SLitExpr)

-- The operators are defined in the same order with its concrete counterparts
-- so that ToCon and ToSym can convert between them correctly
data SOpsExpr
  = SHeadExpr (UnionM SExpr)
  | SAndExpr (UnionM SExpr) (UnionM SExpr)
  | SConsExpr (UnionM SExpr) (UnionM SExpr)
  | STailExpr (UnionM SExpr)
  | SOrExpr (UnionM SExpr) (UnionM SExpr)
  | SNotExpr (UnionM SExpr)
  deriving (Show, Generic)
  deriving (Mergeable SymBool, ToSym OpsExpr, Evaluate Model) via (Default SOpsExpr)

-- These template haskell splices generates helper functions for creating data structures wrapped in UnionM
$(makeUnionMWrapper "u" ''SExpr)
$(makeUnionMWrapper "u" ''SLitExpr)
$(makeUnionMWrapper "u" ''SOpsExpr)

-- For example, the following code are equivalent
-- Also note that, thanks to the OverloadedStrings,
-- the user can create simple named symbolic constants with string literals.
createdFromStrLit :: SymBool
createdFromStrLit = "a"

v1 :: UnionM SLitExpr
v1 = mrgReturn $ SBoolLit "a"

v2 :: UnionM SLitExpr
v2 = uSBoolLit "a"

-- The error type.
-- TypeError is a type error thrown by the type checker
-- EvalTypeError is a type error thrown by the interpreter.
-- This should not be thrown when interpreting a well-typed program.
-- EvalRuntimeError is some error (other than the type error) thrown by the interpreter
data Error = TypeError | EvalTypeError | EvalRuntimeError
  deriving (Show, Generic)
  deriving (Mergeable SymBool) via (Default Error)

data Type = BoolType | ListType
  deriving (Show, Eq, Generic)
  deriving (Mergeable SymBool) via (Default Type)

-- Helper for typing / interpreting unary operators
unary ::
  (Mergeable SymBool a) =>
  (SExpr -> ExceptT Error UnionM a) ->
  UnionM SExpr ->
  (a -> ExceptT Error UnionM a) ->
  ExceptT Error UnionM a
unary f v comb = do
  vt <- lift v >>= f
  comb vt

-- Helper for typing / interpreting binary operators
binary ::
  (Mergeable SymBool a) =>
  (SExpr -> ExceptT Error UnionM a) ->
  UnionM SExpr ->
  UnionM SExpr ->
  ((a, a) -> ExceptT Error UnionM a) ->
  ExceptT Error UnionM a
binary f l r comb = do
  lt <- lift l >>= f
  rt <- lift r >>= f
  curry comb lt rt

-- The type checker function. This implementation is correct.
-- We will synthesis programs with it, and we will verify its correctness.
stypeCheck :: SExpr -> ExceptT Error UnionM Type
stypeCheck (SLit (SBoolLit _)) = mrgReturn BoolType
stypeCheck (SLit (SListLit _)) = mrgReturn ListType
stypeCheck (SOps (SHeadExpr e)) = do
  typ <- lift e >>= stypeCheck
  if typ == ListType then mrgReturn BoolType else throwError TypeError
stypeCheck (SOps (SAndExpr l r)) = binary stypeCheck l r $ \case
  (BoolType, BoolType) -> mrgReturn BoolType
  _ -> throwError TypeError
stypeCheck (SOps (SConsExpr l r)) = binary stypeCheck l r $ \case
  (BoolType, ListType) -> mrgReturn ListType
  _ -> throwError TypeError
stypeCheck (SOps (STailExpr e)) = unary stypeCheck e $ \case
  ListType -> mrgReturn ListType
  _ -> throwError TypeError
stypeCheck (SOps (SOrExpr l r)) = binary stypeCheck l r $ \case
  (BoolType, BoolType) -> mrgReturn BoolType
  _ -> throwError TypeError
stypeCheck (SOps (SNotExpr e)) = unary stypeCheck e $ \case
  BoolType -> mrgReturn BoolType
  _ -> throwError TypeError

-- Note that we don't have to implement the concrete type checker,
-- if you want one, you can do
typeCheck :: Expr -> Except Error Type
typeCheck e = fromJust $ toCon $ stypeCheck (toSym e)

interpretHead :: [SymBool] -> ExceptT Error UnionM SymBool
interpretHead [] = throwError TypeError
interpretHead (x : _) = mrgReturn x

interpretTail :: [SymBool] -> ExceptT Error UnionM (UnionM [SymBool])
interpretTail [] = throwError TypeError
interpretTail (_ : xs) = mrgReturn $ mrgReturn xs

-- The interpreter function.
sinterpret :: SExpr -> ExceptT Error UnionM SLitExpr
sinterpret (SLit v) = mrgReturn v
sinterpret (SOps (SHeadExpr e)) = unary sinterpret e $ \case
  SListLit l -> mrgFmap SBoolLit $ lift l >>= interpretHead
  _ -> throwError EvalTypeError
sinterpret (SOps (SAndExpr l r)) = binary sinterpret l r $ \case
  (SBoolLit lb, SBoolLit rb) -> mrgReturn $ SBoolLit $ lb &&~ rb
  _ -> throwError EvalTypeError
sinterpret (SOps (SConsExpr l r)) = binary sinterpret l r $ \case
  (SBoolLit lb, SListLit rl) -> mrgReturn $ SListLit $ mrgFmap (lb :) rl
  _ -> throwError EvalTypeError
sinterpret (SOps (STailExpr e)) = unary sinterpret e $ \case
  SListLit l -> mrgFmap SListLit $ lift l >>= interpretTail
  _ -> throwError EvalTypeError
sinterpret (SOps (SOrExpr l r)) = binary sinterpret l r $ \case
  (SBoolLit lb, SBoolLit rb) -> mrgReturn $ SBoolLit $ lb ||~ rb
  _ -> throwError EvalTypeError
sinterpret (SOps (SNotExpr e)) = unary sinterpret e $ \case
  SBoolLit eb -> mrgReturn $ SBoolLit $ nots eb
  _ -> throwError EvalTypeError

-- Combined type checker and interpreter function
-- See the main function for a sample result
run :: SExpr -> ExceptT Error UnionM SLitExpr
run e = stypeCheck e >> mrgReturn () >> sinterpret e

-- Generating a symbolic SLitExpr. The specification type is Integer, which is the maximum length of the lists.
-- See the main function for a sample generated value
--
-- In the current paper, this class is called SymGen, and genSymFresh is called fresh.
-- We are still thinking about its naming.
instance GenSym SymBool Integer SLitExpr where
  genSymFresh listLength = do
    b :: SymBool <- genSymSimpleFresh @SymBool () -- This @SymBool is required. It's the symbolic boolean we are using.
    l :: UnionM [SymBool] <- genSymFresh listLength
    choose [SBoolLit b, SListLit l]

-- The specification for generating an SExpr. The first field is the maximum AST depth,
-- and the second field is the maximum length of the list literals.
data SExprSpec = SExprSpec Integer Integer

instance GenSym SymBool SExprSpec SExpr where
  genSymFresh (SExprSpec depth listLength) =
    if depth <= 1
      then do
        lit <- genSymFresh listLength
        return $ mrgFmap SLit lit
      else do
        l0 <- genSymFresh (SExprSpec 0 listLength)
        l1 <- genSymFresh (SExprSpec (depth - 1) listLength)
        l2 <- genSymFresh (SExprSpec (depth - 1) listLength)
        lops <- choose $ SOps <$> [SHeadExpr l1, SAndExpr l1 l2, SConsExpr l1 l2, STailExpr l1, SOrExpr l1 l2, SNotExpr l2]
        chooseU [l0, lops]

-- Synthesis specification
-- The LitExpr, which is a literal, is the desired evaluation result
newtype SynthSpec = SynthSpec LitExpr

-- In the paper, SolverErrorTranslation and SolverTranslation are the same class.
-- The SolverErrorTranslation type class was decoupled from the solver translation type class now.
-- The errorTranslation function defines whether abnormal termination paths due to specific exception is desired.
instance SolverErrorTranslation SynthSpec Error where
  -- For synthesis task, we don't want our synthesized program to terminate abnormally.
  errorTranslation _ _ = False

-- The valueTranslation function defines if a path terminates normally without an exception,
-- what is the desired property of the evaluation result
instance SolverTranslation SynthSpec SymBool Error SLitExpr where
  -- For synthesis task, we expect that the result is equivalent to the specification
  -- toSym comes from the ToSym type class, and converts LitExpr to SLitExpr.
  -- ==~ comes from the SEq type class, and constructs a SymBool (which wraps a formula) to represent
  -- the equivalence condition
  valueTranslation (SynthSpec lit) res = toSym lit ==~ res

data VerifSpec = VerifSpec

instance SolverErrorTranslation VerifSpec Error where
  -- For verification task, we are going to find counterexamples that does not crash the type checker,
  -- but crashes the interpreter due to a type error.
  errorTranslation _ EvalTypeError = True
  errorTranslation _ _ = False

instance SolverTranslation VerifSpec SymBool Error SLitExpr where
  -- A counterexample should not terminate normally
  valueTranslation _ _ = conc False

-- A buggy typer
stypeCheckBad :: SExpr -> ExceptT Error UnionM Type
stypeCheckBad (SLit (SBoolLit _)) = mrgReturn BoolType
stypeCheckBad (SLit (SListLit _)) = mrgReturn ListType
stypeCheckBad (SOps (SHeadExpr e)) = do
  typ <- lift e >>= stypeCheck
  if typ == ListType then mrgReturn BoolType else throwError TypeError
stypeCheckBad (SOps (SAndExpr l r)) = binary stypeCheck l r $ \case
  (BoolType, BoolType) -> mrgReturn BoolType
  _ -> throwError TypeError
stypeCheckBad (SOps (SConsExpr l r)) = binary stypeCheck l r $ \case
  -- Here a bug is injected. The type signature for rhs should not be Bool
  (BoolType, BoolType) -> mrgReturn ListType
  _ -> throwError TypeError
stypeCheckBad (SOps (STailExpr e)) = unary stypeCheck e $ \case
  ListType -> mrgReturn ListType
  _ -> throwError TypeError
stypeCheckBad (SOps (SOrExpr l r)) = binary stypeCheck l r $ \case
  (BoolType, BoolType) -> mrgReturn BoolType
  _ -> throwError TypeError
stypeCheckBad (SOps (SNotExpr e)) = unary stypeCheck e $ \case
  BoolType -> mrgReturn BoolType
  _ -> throwError TypeError

runBad :: SExpr -> ExceptT Error UnionM SLitExpr
runBad e = stypeCheckBad e >> mrgReturn () >> sinterpret e

main :: IO ()
main = do
  -- We are using z3 solver, with unbounded reasoning.
  -- Unbounded reasoning means that we won't do approximation on integers, and we are reasoning using unbounded integers,
  -- the result would be sound, but the reasoning could possibly be slower in some scenario.
  let solverConfig = UnboundedReasoning z3
  let sketch = runGenSymFresh (genSymFresh $ SExprSpec 3 2) "a" :: UnionM SExpr
  let sketchRunResult = lift sketch >>= run

  let verbosePrint = False

  putStrLn "------ sketch ------"
  putStr "Lit sketch: "
  -- Here prints a sketch for literal expressions generated by GenSym class.
  -- Usually this is a very large object, representing a large program space in a compact way,
  -- and is not human-readable.
  -- Lit sketch: UMrg (If name@7 (Single (SBoolLit name@0)) (Single (SListLit (UMrg (If name@4 (Single []) (If name@5 (Single [name@3]) (If name@6 (Single [name@2,name@3]) (Single [name@1,name@2,name@3]))))))))
  print (runGenSymFresh (genSymFresh (3 :: Integer)) "name" :: UnionM SLitExpr)
  -- Caveat: long output if you turn on verbosePrint
  when verbosePrint $ do
    putStr "Full sketch: "
    print sketch

  putStrLn "------ execution ------"
  -- Construct a symbolic program. The solver can decide if the program should be an 'and' or a 'cons'
  -- if a (and b c) (cons b [c])
  let symbolicProgram1 :: UnionM SExpr =
        mrgIf
          "a"
          (mrgReturn $ SOps $ SAndExpr (mrgReturn $ SLit $ SBoolLit "b") (mrgReturn $ SLit $ SBoolLit "c"))
          (mrgReturn $ SOps $ SConsExpr (mrgReturn $ SLit $ SBoolLit "b") (mrgReturn $ SLit $ SListLit $ mrgReturn ["c"]))
  -- Type check it.
  -- There should not be type errors, and the path conditions will be maintained.
  print $ lift symbolicProgram1 >>= stypeCheck
  -- ExceptT (UMrg (If a (Single (Right BoolType)) (Single (Right ListType))))

  -- Evaluate it.
  -- There should not be errors, and the path conditions will be maintained.
  print $ lift symbolicProgram1 >>= sinterpret
  -- ExceptT (UMrg (If a (Single (Right (SBoolLit (&& b c)))) (Single (Right (SListLit (UMrg (Single [b,c])))))))

  -- First type check, then evaluate.
  print $ lift symbolicProgram1 >>= run
  -- ExceptT (UMrg (If a (Single (Right (SBoolLit (&& b c)))) (Single (Right (SListLit (UMrg (Single [b,c])))))))

  -- Define some wrapper functions to make creation simpler
  let sAndExpr l r = uSOps $ SAndExpr l r
  let sConsExpr l r = uSOps $ SConsExpr l r
  let sBoolLit = uSLit @SymBool @UnionM . SBoolLit
  let sListLit = uSLit @SymBool @UnionM . SListLit . mrgReturn

  -- Construct a symbolic program. If a is true and c is false, then the program is (and b [d]),
  -- and is not well-typed.
  -- if a (and b (if c d [d])) (cons b [c])
  let symbolicProgram2 :: UnionM SExpr =
        mrgIf
          "a"
          (sAndExpr (sBoolLit "b") (mrgIf "c" (sBoolLit "d") (sListLit ["d"])))
          (sConsExpr (sBoolLit "b") (sListLit ["c"]))

  -- Type check it.
  print $ lift symbolicProgram2 >>= stypeCheck
  -- ExceptT (UMrg (If (&& a (! c)) (Single (Left TypeError)) (If a (Single (Right BoolType)) (Single (Right ListType)))))
  -- This result means that if a /\ not c, our symbolic program would be and b [d], which does not type check

  -- Evaluate it.
  print $ lift symbolicProgram2 >>= sinterpret
  -- ExceptT (UMrg (If (&& a (! c)) (Single (Left EvalTypeError)) (If a (Single (Right (SBoolLit (&& b d)))) (Single (Right (SListLit (UMrg (Single [b,c]))))))))
  -- This result means that if a /\ not c, our symbolic program would be and b [d], which does not type check, and can crash the interpreter

  -- First type check, then evaluate.
  print $ lift symbolicProgram2 >>= run
  -- ExceptT (UMrg (If (&& a (! c)) (Single (Left TypeError)) (If a (Single (Right (SBoolLit (&& b d)))) (Single (Right (SListLit (UMrg (Single [b,c]))))))))
  -- This result means that if a /\ not c, our symbolic program would be and b [d], which does not type check.
  -- As the type error is already detected by the typer, that symbolic program won't further crash the interpreter again

  -- Synthesis a program that evaluates to a list with four elements.
  -- As our sketch is only allowed to contain list literals with length <= 2,
  -- the result has to be constructed using ConsExpr
  putStrLn "------ synthesis and verification ------"
  synthRes <- solveWithExcept (SynthSpec $ ListLit [True, False, True, False]) solverConfig sketchRunResult
  case synthRes of
    Left _ -> putStrLn "Synthesis failed"
    Right mo -> putStr "Synthesized expression: " >> print (evaluateToCon mo sketch :: Expr)
  -- output: Synthesized expression: Ops (ConsExpr (Lit (BoolLit True)) (Ops (ConsExpr (Lit (BoolLit False)) (Lit (ListLit [True,False])))))

  -- Tries to verify the correct typer. We will not get a counter example
  verifCorrectRes <- solveWithExcept VerifSpec solverConfig sketchRunResult
  case verifCorrectRes of
    Left _ -> putStrLn "Verified"
    Right mo -> putStr "Verification failed, counterexample: " >> print (evaluateToCon mo sketch :: Expr)
  -- output: Verified

  -- Tries to verify the incorrect typer. We will get a counter example
  let sketchRunBadResult = lift sketch >>= runBad
  verifBadRes <- solveWithExcept VerifSpec solverConfig sketchRunBadResult
  case verifBadRes of
    Left _ -> putStrLn "Verified"
    Right mo -> putStr "Verification failed, counterexample: " >> print (evaluateToCon mo sketch :: Expr)
  -- output: Verification failed, counterexample: Ops (ConsExpr (Lit (BoolLit False)) (Ops (HeadExpr (Lit (ListLit [False,False])))))
