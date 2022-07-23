{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Tutorial.Sudoku.Sudoku
  ( -- * Preface

    -- | In this tutorial, we will build a sudoku solver.
    -- We will show
    --
    --   (1) how to use symbolic primitive types in Grisette, and
    --
    --   (2) how Grisette supports user defined data types, and
    --
    --   (3) how to interact with the solver with Grisette.
    --
    -- We recommend reading against the source code of this tutorial.

    -- * Data Structures

    -- | Grisette provides the support for some primitive types directly supported by SMT solvers.
    -- Currently, Grisette provided native support for the symbolic counterparts of
    -- 'Integer', 'Bool', @'SignedBV' n@ and @'UnsignedBV'@ n types.
    -- They can be accessed via @'Sym' 'Integer'@, @'Sym' 'Bool'@, @'Sym' ('SignedBV' n)@ and @'Sym' ('UnsignedBV' n)@.
    -- Grisette also provides the support for fixed bitwidth signed and unsigned integer types @Int*@ and @Word*@,
    -- e.g. 'Data.Int.Int8', 'Data.Word.Word32', etc.
    -- The symbolic counterparts of these types are symbolic signed and unsigned bitvectors.
    --
    -- The unique feature of symbolic primitive types is that they can contain symbolic constants.
    -- A symbolic constant can be thinked as a placeholder for a concrete constant of the same type,
    -- and the actual constant value of them will be determined with the SMT solvers.
    --
    -- Grisette provides a similar API for these symbolic primitive types as their concrete counterparts.
    -- For example, '&&~' is the symbolic version of 'Data.Bool.&&', and @'Sym' 'Integer'@ types has the 'Num' instance,
    -- and the common '+', '-' operators are available for them.
    -- See "Grisette.Core" for the details.
    --
    -- In this section, we will define the concrete and symbolic puzzle board type,
    -- and integrate them seamlessly into the Grisette ecosystem.
    -- We will achieve this by implementing a set of type classes,
    -- and most of them can be automatically derived.
    Row,
    SymRow,
    -- | In Grisette, all functionalities are provided by the type class instances.
    -- For example, 'ToCon' type class instance will convert a concrete type to a symbolic type,
    -- and 'ToSym' type class instance will convert a symbolic type to a concrete type.
    -- There are more type class instances available in "Grisette.Core", and we implemented some of them for
    -- 'Board' and 'SymBoard'.
    -- See the following code and the documentation of "Grisette.Core" for more details.
    Board (..),
    SymBoard (..),

    -- * Sudoku solver

    -- | The Sudoku solver is simple.
    -- The 'check' function will check whether the 9 symbolic integers in a row, column or square
    -- are distinct and are in the range 1-9.
    --
    -- The 'valid' function will check whether a symbolic board has the correct shape,
    -- and check the rows, columns and squares with 'check' function.
    --
    -- The 'sudoku' function will construct a symbolic board from the given concrete board specification,
    -- then construct the constraints with 'valid' and send the constraints to the solver.
    -- With the solver response, it will evaluate the symbolic board back to concrete.
    check,
    valid,
    sudoku,

    -- * Example puzzles
    easy,
    medium,
    hard,
    expert,

    -- * Driver function
    main,
  )
where

import Data.List
import GHC.Generics
import Grisette

-- | Concrete row type. A sequence of 'Integer's.
type Row = [Integer]

-- | Symbolic row type. A sequence of 'SymInteger's.
type SymRow = [SymInteger]

-- | Concrete Sudoku board type. It's a sequence of 'Row's.
-- 1-9 are entries that are filled in. Other numbers represent empty entries that needs to be filled in by the solver.
--
-- The concrete sudoku board type will be used mainly for two purposes:
--
-- (1) pretty printing, and
-- (2) easy construction as a specification.
--
-- We declare it as a newtype for implementing custom type class instances.
newtype Board = Board [Row]
  deriving
    ( -- | For printing a concrete board. For symbolic boards with all entries filled in,
      -- they will be printed by first converting them to concrete, and then printing.
      Show,
      -- | For type class derivation. Grisette provides a default implementation for ADTs for most type classes
      -- provided.
      -- You can use the @DerivingVia@ extension and the 'Default' type wrapper to derive the default
      -- implementation for other type classes.
      -- See the code for more details.
      Generic
    )
  deriving
    ( -- | Enable conversion from 'SymBoard' to 'Board'.
      -- 'ToCon' provides the 'toCon' function, which has the type signature:
      -- @toCon :: SymBoard -> Maybe Board@.
      --
      -- It can only convert a symbolic board with all entries filled in, or it will return a 'Nothing'.
      ToCon SymBoard
    )
    via (Default Board)

-- | Symbolic Sudoku board type. It's a sequence of 'SymRow's.
newtype SymBoard = SymBoard [SymRow]
  deriving
    ( -- | For type class derivation.
      Generic
    )
  deriving
    ( -- | Not used in this example, but you need this for implementing 'GenSym'.
      --
      -- 'Mergeable' enables the merging of symbolic boards in a 'UnionLike' container.
      -- We will not elaborate on this now.
      Mergeable SymBool,
      -- | Enable conversion from 'Board' to 'SymBoard'.
      -- 'ToSym' provides the 'toSym' function, which has the type signature:
      -- @toSym :: Board -> SymBoard@.
      ToSym Board,
      -- | Enable evaluating 'SymBoard' from the solver models.
      --
      -- If the solver returns a satisfiable model, we can replace all the symbolic constants with the actual value
      -- in the model with the 'Evaluate' type class instance.
      Evaluate Model
    )
    via (Default SymBoard)

-- | Not used in this example, but it is a prerequisite for 'GenSymSimple',
-- and the member functions will be automatically derived if 'GenSymSimple' instance is presented.
instance GenSym SymBool Board SymBoard

-- | Generates symbolic board sketch for the solver to fill in.
-- All the entries in the concrete board with a number less than 1 or greater than 9 will be set as a hole (symbolic constant).
--
-- The solver will be used to determine the concrete assignments of the symbolic constants.
--
-- 'genSymSimpleFresh' function generates unique symbolic values in a 'MonadSymGenFresh' environment with a specification.
-- For symbolic primitive types, 'genSymSimpleFresh' will generate a unique symbolic constant from no specifications (represented as unit values).
-- For complex types, 'genSymSimpleFresh' can generate symbolic variables containing symbolic constants.
instance GenSymSimple Board SymBoard where
  genSymSimpleFresh (Board b) =
    SymBoard
      <$> traverse
        ( traverse
            ( \case
                x | x <= 0 || x > 9 ->
                  -- As Grisette is configurable with different symbolic primitive implementations,
                  -- this @SymBool annotation is required for disambiguation.
                  -- The '()' is the specification for the symbolic integers.
                  genSymSimpleFresh ()
                x ->
                  -- The 'conc' call wraps a concrete value into a symbolic value.
                  return $ conc x
            )
        )
        b

-- | Check if a row, column or square complies with the Sudoku constraint.
--
-- Symbolic versions of the operations are used here.
check :: SymRow -> SymBool
check [] = conc True
-- '&&~' is the symbolic version of 'Data.Bool.&&', and it is a symbolic conjunction.
check (x : xs) = distinct x xs &&~ inbound x &&~ check xs
  where
    distinct _ [] = conc True
    -- '/=~' is the symbolic version of '/=', and it is symbolic inequality.
    distinct x1 (y : ys) = x1 /=~ y &&~ distinct x1 ys
    -- '>~' is the symbolic version of '>', and it is the symbolic greater than relation.
    inbound x1 = x1 >~ 0 &&~ x1 <=~ 9

-- | Constraints the symbolic board to comply with the Sudoku constraint.
valid :: SymBoard -> SymBool
valid (SymBoard rows) =
  foldl (\acc x -> acc &&~ check x) (conc sizesOk) (rows ++ columns ++ squares)
  where
    sizesOk = length rows == 9 && all (\r -> length r == 9) rows
    columns = transpose rows
    chunks = concat $ transpose <$> chunk3 rows
    squares = concat <$> chunk3 chunks
    chunk3 (x1 : x2 : x3 : xs) = [x1, x2, x3] : chunk3 xs
    chunk3 _ = []

-- | Solve a sudoku.
-- With the 'GenSymSimple' type class instances,
-- the 'genSymSimple' function is used to generate a symbolic board sketch from a concrete board specification.
--
-- The solver would be called with the 'solveFormula' function with a solver configuration, which has the type signature:
-- 'GrisetteSMTConfig n'.
-- The solver configuration consists of two parts:
--
-- (1) whether we should perform finitization, and
-- (2) which solver and its options to use.
--
-- For the finitization,
--
-- (1) 'UnboundedReasoning' means that no finitization is performed. With this option, the solver would perform unbounded reasoning
-- for symbolic integers. This option is sound, but it can be very slow.
--
-- (2) 'BoundedReasoning' means that the solver would perform bounded reasoning for symbolic integers. With this option, the system
-- assumes that the symbolic integers are bounded bitvectors. This option is usually much faster, but when overflows are possible,
-- the reasoning will not be sound and may yield wrong results.
--
-- For the solver and its options, we currently use the solver configurations provided by the [@sbv@](https://hackage.haskell.org/package/sbv)
-- package.
-- For example, you can use 'z3' from @sbv@ to solve the problem.
--
-- The solver will return an 'Either' type, and 'Left' values indicate that the solver failed to solve the problem.
-- The 'Right' value wraps a 'Model' type, which contains the solution.
-- The symbolic board can be evaluated and converted to concrete board with the model using the 'Evaluate' and 'ToCon' type class.
sudoku :: GrisetteSMTConfig n -> Board -> IO (Maybe Board)
sudoku config board = do
  -- generate the symbolic board sketch
  let symboard = genSymSimple board "a"
  -- call the solver with the given configuration
  m <- solveFormula config $ valid symboard
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateToCon mo symboard

easy :: Board
easy =
  Board
    [ [0, 0, 0, 0, 0, 0, 0, 8, 0],
      [6, 8, 0, 4, 7, 0, 0, 2, 0],
      [0, 1, 9, 5, 0, 8, 6, 4, 7],
      [0, 6, 0, 9, 0, 0, 0, 0, 4],
      [3, 4, 2, 6, 8, 0, 0, 0, 0],
      [1, 9, 0, 0, 5, 0, 8, 3, 0],
      [0, 0, 0, 7, 2, 0, 4, 0, 3],
      [0, 0, 6, 0, 0, 5, 0, 1, 0],
      [0, 0, 3, 8, 9, 1, 5, 0, 0]
    ]

medium :: Board
medium =
  Board
    [ [8, 0, 0, 1, 0, 0, 0, 7, 0],
      [0, 2, 0, 0, 4, 0, 8, 0, 0],
      [0, 6, 0, 7, 0, 0, 0, 0, 0],
      [0, 0, 0, 4, 7, 0, 9, 0, 8],
      [2, 4, 0, 0, 8, 0, 0, 0, 0],
      [0, 3, 8, 0, 0, 0, 0, 0, 5],
      [0, 8, 0, 6, 0, 4, 1, 0, 0],
      [9, 0, 0, 0, 0, 7, 2, 0, 4],
      [0, 0, 5, 8, 1, 0, 0, 0, 6]
    ]

hard :: Board
hard =
  Board
    [ [0, 2, 4, 0, 0, 0, 0, 0, 7],
      [0, 6, 7, 0, 0, 0, 3, 0, 2],
      [0, 0, 0, 0, 4, 0, 5, 0, 0],
      [0, 0, 6, 0, 3, 0, 8, 5, 0],
      [4, 0, 5, 0, 8, 0, 0, 2, 0],
      [0, 0, 0, 0, 0, 0, 0, 7, 0],
      [7, 0, 0, 3, 0, 2, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 8, 0, 0, 4, 0, 0, 9]
    ]

expert :: Board
expert =
  Board
    [ [0, 7, 0, 0, 0, 0, 8, 0, 0],
      [8, 3, 1, 0, 0, 4, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0, 0, 0],
      [0, 5, 7, 0, 6, 0, 0, 2, 0],
      [3, 0, 0, 0, 0, 1, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 9, 6, 0],
      [4, 0, 0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 3, 0, 0, 6, 0, 5],
      [0, 0, 0, 1, 0, 0, 2, 9, 0]
    ]

main :: IO ()
main = do
  -- here we will use z3 solver, and finitize the integers to bitwidth 5.
  -- As no overflow would happen, it is sound here.
  let config = BoundedReasoning @5 z3
  sudoku config easy >>= print
  sudoku config medium >>= print
  sudoku config hard >>= print
  sudoku config expert >>= print
