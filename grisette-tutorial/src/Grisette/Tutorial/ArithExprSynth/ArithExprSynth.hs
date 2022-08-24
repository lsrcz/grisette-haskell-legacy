{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Tutorial.ArithExprSynth.ArithExprSynth
  ( -- * Preface

    -- | In this tutorial, we will build an arithmetic expression synthesizer.
    -- We will show how to work with complex symbolic types with the 'UnionM' monad
    --
    -- We recommend reading against the source code of this tutorial.

    -- * Data Structures

    -- | Similar as the previous chapter, we will first define the concrete and symbolic data structures.
    -- One difference here is that the data structure is recursive and much more complex.
    --
    -- To maximize merging, some fields in 'SymExpr' are wrapped with 'UnionM'.
    -- The 'UnionM' is a monadic container for path condition guarded values.
    -- With the 'Mergeable' instances, the values contained in the 'UnionM' may be merged.
    -- Here we can merge the values with the same constructors.
    --
    -- With the current definition, @if cond then (1 + 2) + 3 else (2 - 1) + 4@ can be represented with a single
    -- 'SymAdd' value. The result will have the same structure as follows.
    -- The (+3) and (+4) are merged together.
    --
    -- @Add (if cond then Add 1 2 else Sub 2 1) (ite cond 3 4)@
    --
    -- This approach will consolidate similar information as much as possible,
    -- and reduce the need for the interpreter to execute on multiple paths,
    -- thus improve the symbolic execution performance.
    Expr (..),
    SymExpr (..),
    Op,

    -- * Helpful Constructor Wrappers

    -- |
    -- #helpful-constructor-wrappers#
    -- The following definitions are generated with
    --
    -- > $(makeUnionMWrapper "u" ''SymExpr)
    --
    -- They are useful when building 'SymExpr' manually. Compare the following definitions:
    --
    -- > let a :: SymExpr = SymAdd (mrgReturn $ SymLiteral 1) (mrgReturn $ SymSub (mrgReturn $ SymLiteral 2) (mrgReturn $ SymLiteral 3))
    -- > let b :: SymExpr = SymAdd (uSymLiteral 1) (uSymSub (uSymLiteral 2) (uSymLiteral 3))
    uSymLiteral,
    uSymAdd,
    uSymSub,

    -- * Interpreter and Synthesizer
    interpret,
    synthExpr,

    -- * Program sketch
    sketch,

    -- * Driver function
    main,
  )
where

import Data.Proxy
import GHC.Generics
import Grisette

-- | Concrete Expression type.
data Expr
  = -- | Integer literals.
    Literal Integer
  | -- | Addition node.
    Add Expr Expr
  | -- | Subtraction node.
    Sub Expr Expr
  deriving (Show, Generic)
  deriving (ToCon SymExpr) via (Default Expr)

-- | Symbolic Expression type.
--
-- 'UnionM's are used to wrap the fields of 'SymExpr' to help merging efficiently.
data SymExpr
  = -- | Symbolic integer literals.
    -- The 'SymInteger' type allows us to have symbolic holes in our expressions.
    --
    -- Note that we don't have to wrap 'SymInteger' in a 'UnionM' because 'SymInteger'
    -- (and other symbolic primitives)
    -- is capable to be merged efficiently without the help of 'UnionM'.
    --
    -- Such types have the 'SimpleMergeable' instance,
    -- you can refer to the documentation for more details.
    SymLiteral SymInteger
  | -- | Symbolic Addition node. The fields are wrapped in 'UnionM' to help merging.
    SymAdd (UnionM SymExpr) (UnionM SymExpr)
  | -- | Symbolic Subtraction node. The fields are wrapped in 'UnionM' to help merging.
    SymSub (UnionM SymExpr) (UnionM SymExpr)
  deriving (Show, Generic)
  deriving
    ( ToSym Expr,
      -- | Useful here as we need to wrap 'SymExpr' in 'UnionM's
      --
      -- This instance tells Grisette how to merge the results.
      --
      -- For example:
      --
      -- > mrgIf cond (uSymAdd a b) (uSymAdd c d)
      --
      -- will be equivalent to:
      --
      -- > uSymAdd (mrgIf cond a c) (mrgIf cond b d)
      --
      -- This helps avoid path explosion.
      --
      -- 'mrgIf' is a combinator that takes a condition and two values. It has the semantics similar to
      -- 'if' in Haskell, but maintains both the two branches in the resulting 'UnionM' structure with the curresponding path conditions,
      -- and try to merge the results.
      --
      -- Here the @u@-prefixed functions are smart constructors that wraps the result in 'UnionM'.
      -- See [Helpful Constructor Wrappers](#helpful-constructor-wrappers) section for more details.
      Mergeable SymBool,
      Evaluate Model
    )
    via (Default SymExpr)

$(makeUnionMWrapper "u" ''SymExpr)

-- | The operator type. We will use the 'GenSym' infrastructure to directly generate operators.
--
-- Note that the result type must be @'UnionM' 'SymExpr'@.
-- This allows us to merge the operators and push the conditions into the resulting 'UnionM'.
--
-- The following two definitions are equivalent, and will type check.
--
-- > mrgIte cond (uSymAdd :: Op) (uSymSub :: Op)
-- > (\l r -> mrgIf cond (uSymAdd l r) (uSymSub l r)) :: Op
type Op = UnionM SymExpr -> UnionM SymExpr -> UnionM SymExpr

instance GenSym SymBool () Op

-- | Generating fresh symbolic operators can be easily achieved by 'simpleChoose' call.
--
-- In Grisette, there are several such APIs for symbolic choices, for example, 'choose', 'simpleChoose' and 'chooseU'.
--
-- They introduces fresh symbolic boolean variables, and use them to conditionally select one of the provided expressions.
instance GenSymSimple () Op where
  genSymSimpleFresh _ = simpleChoose (Proxy @SymBool) [uSymAdd, uSymSub]

-- | The symbolic interpreter interprets a symbolic expression to a symbolic integer.
--
-- There are two useful things to know about the 'UnionM' container.
--
-- The first is that 'UnionM' is a monadic container.
-- As a container, it contains multiple values guarded by path conditions.
-- Binding a 'UnionM' with a function can be viewed as
-- splitting the execution into multiple paths.
-- Each path corresponds to a value in the 'UnionM' and maintains the corresponding path condition.
-- As an example, the 'SymAdd' branch is implemented with do-block.
-- The 'getSingle' call extracts the 'SymInteger' out from the 'UnionM'.
-- This is safe as we can always merge 'SymInteger' into a single value with the 'SimpleMergeable' instance.
--
-- The second is that Grisette provides some useful combinators for writing code with 'UnionM'.
-- The 'interpret' function accepts 'SymExpr' as an argument, but for recursive calls,
-- we need to call this function on 'UnionM SymExpr'. One possible way to do this is to extract
-- the value out of the 'UnionM' with monadic binds,
-- But for this kind of recursive calls, which is very prevalent, Grisette provided convenient
-- combinator '(#~)'.
--
-- > interpret #~ r
--
-- is equivalent to
--
-- > getSingle $ mrgFmap interpret r
interpret :: SymExpr -> SymInteger
interpret (SymLiteral v) = v
interpret (SymAdd l r) = getSingle $ do
  vl <- l
  vr <- r
  mrgReturn $ interpret vl + interpret vr
interpret (SymSub l r) = interpret #~ l - interpret #~ r

-- | Similar to the synthesizer in "Grisette.Tutorial.Sudoku.Sudoku".
synthExpr :: GrisetteSMTConfig n -> UnionM SymExpr -> Integer -> IO (Maybe Expr)
synthExpr config expr res = do
  r <- solveFormula config $ interpret #~ expr ==~ conc res
  case r of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateToCon mo expr

-- | Here is a sketch for synthesis. The sketch represents the following program with holes:
--
-- > 1 ?? (2 ?? 4)
--
-- The @??@ represents a hole for the solver to fill in an operator.
--
-- This example shows the composability of 'GenSymFresh' monad.
-- You can generate fresh variables with it without the need to care about uniqueness.
-- The usage is similar to the widely used @Gen@ monad in QuickCheck.
--
-- The 'GenSymFresh' monad also works with other monadic infrastructures, for example, parser monads.
-- This enables more flexible usage of 'GenSymFresh', e.g.,
-- it is possible for the parser to directly build the symbolic sketch.
sketch :: UnionM SymExpr
sketch =
  runGenSymFresh
    ( do
        let v1 :: UnionM SymExpr = uSymLiteral 1
        let v2 :: UnionM SymExpr = uSymLiteral 2
        let v3 :: UnionM SymExpr = uSymLiteral 4
        op1 :: Op <- genSymSimpleFresh ()
        op2 :: Op <- genSymSimpleFresh ()
        return $ op1 v1 (op2 v2 v3)
    )
    $$(nameWithLoc "a")

main :: IO ()
main = do
  let config = UnboundedReasoning z3
  synthExpr config sketch (-1) >>= print
  synthExpr config sketch 7 >>= print
  synthExpr config sketch 0 >>= print
