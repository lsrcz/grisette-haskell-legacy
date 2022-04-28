{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module Grisette.Tutorial.Sudoku.Sudoku
  ( -- * Preface
    -- | In this tutorial, we will build a sudoku solver.
    -- We will show
    --
    --   (1) how to use primitive types in Grisette, and
    --
    --   (2) how Grisette supports user defined data types, and
    --
    --   (3) how to interact with the solver with Grisette.

    -- * Data Structures
    -- | In Grisette, using the primitive symbolic types is similar as using the concrete ones.
    -- Currently, Grisette provided native support for the symbolic counterparts of
    -- 'Integer', 'Bool', 'SignedBV' and 'UnsignedBV'.
    -- Grisette provides operators for the symbolic types, see "Grisette.Core" for the details.
    --
    -- In this section, we will define the concrete and symbolic puzzle board type,
    -- and integrate them seamlessly into the Grisette ecosystem.
    -- We will achieve this by implementing a set of type classes.
    -- Most of them can be automatically derived.
    Row,
    SymRow,
    Board (..),
    SymBoard (..),

    -- * Sudoku solver
    -- | The Sudoku solver is simple.
    -- The 'check' function will check whether the 9 symbolic integers in a row / column / square
    -- are distinct and are in the range 1-9.
    --
    -- The 'valid' function will check whether a symbolic board has the correct shape,
    -- and check the rows / columns / squares with 'check' function.
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

-- | Concrete Sudoku board type. It's a sequence of 9 'Row's.
--
-- We declare it as a newtype for implementing custom type class instances.
newtype Board = Board [Row]
  deriving
    ( -- | For printing.
      Show,
      -- | For type class derivation.
      Generic
    )
  deriving
    ( -- | Enable conversion from 'SymBoard' to 'Board'.
      ToCon SymBoard
    )
    via (Default Board)

-- | Symbolic Sudoku board type. It's a sequence of 9 'SymRow's.
newtype SymBoard = SymBoard [SymRow]
  deriving
    ( -- | For type class derivation.
      Generic
    )
  deriving
    ( -- | Not used in this example, but you need this for implementing 'GenSym'.
      Mergeable SymBool,
      -- | Enable conversion from 'Board' to 'SymBoard'.
      ToSym Board,
      -- | Enable evaluating 'SymBoard' from the solver models.
      Evaluate Model
    )
    via (Default SymBoard)

-- | Not used in this example, but you need this for implementing 'GenSymSimple'.
instance GenSym SymBool Board SymBoard

-- | Generates symbolic board sketch for the solver to fill in.
-- All the entries in the concrete board with a number less than 1 or greater than 9 will be set as a hole.
instance GenSymSimple SymBool Board SymBoard where
  genSymSimpleFresh (Board b) =
    SymBoard
      <$> traverse
        ( traverse
            ( \x ->
                if x <= 0 || x > 9
                  then -- generate fresh symbolic variable
                    genSymSimpleFresh @SymBool ()
                  else -- lift the concrete integer to symbolic integer
                    return $ conc x
            )
        )
        b

-- | Check if a row / column / square complies with the Sudoku constraint.
check :: SymRow -> SymBool
check [] = conc True
check (x : xs) = distinct x xs &&~ inbound x &&~ check xs
  where
    distinct _ [] = conc True
    distinct x1 (y : ys) = x1 /=~ y &&~ distinct x1 ys
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
sudoku :: GrisetteSMTConfig n -> Board -> IO (Maybe Board)
sudoku config board = do
  -- generate the symbolic board sketch
  let symboard = genSymSimple @SymBool board "a"
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
  -- here we will use z3 solver, and finitize the integers to bitwidth 5. It is sound here.
  let config = BoundedReasoning @5 z3
  sudoku config easy >>= print
  sudoku config medium >>= print
  sudoku config hard >>= print
  sudoku config expert >>= print
