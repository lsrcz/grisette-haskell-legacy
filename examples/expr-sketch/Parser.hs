{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Parser where

import Control.Monad.Combinators.Expr
import Control.Monad.State as ST
import qualified Data.ByteString as B
import Data.Void
import Expr
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymGen
import Grisette.Data.SymPrim
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Text.Megaparsec.Byte.Lexer as L
import Grisette.Data.Class.PrimWrapper

type Parser = ParsecT Void B.ByteString (ST.State SymGenState)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: B.ByteString -> Parser B.ByteString
symbol = L.symbol space

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

concIntExpr :: Parser (UnionM SymbExpr)
concIntExpr = mrgSingle . SConstantExpr <$> lexeme L.decimal

intlst :: Parser [Integer]
intlst = between (symbol "??[") (symbol "]") (sepBy1 L.decimal (symbol ","))

intHoleRangeExpr :: Parser (UnionM SymbExpr)
intHoleRangeExpr = do
  l <- intlst
  let x = conc @SymInteger <$> l
  i <- choose @SymBool (head x) (tail x)
  return $ mrgSingle $ SConstantExpr $ getSingle i

intHoleExpr :: Parser (UnionM SymbExpr)
intHoleExpr = do
  _ <- symbol "??i"
  i <- genSymSimpleIndexed @SymBool ()
  return $ mrgSingle $ SConstantExpr i

binary :: B.ByteString -> (a -> a -> a) -> Operator Parser a
binary name f = InfixL (f <$ symbol name)

opHoleOperator :: Operator Parser (UnionM SymbExpr)
opHoleOperator = InfixL $ do
  _ <- symbol "??op"
  genSymSimpleIndexed @SymBool [Add, Sub, Mul]

addOp :: Parser Op
addOp = symbol "+" >> return Add

subOp :: Parser Op
subOp = symbol "-" >> return Sub

mulOp :: Parser Op
mulOp = symbol "*" >> return Mul

oplst :: Parser [Op]
oplst = between (symbol "??{") (symbol "}") (sepBy (choice [addOp, subOp, mulOp]) (symbol ","))

opBetterHole :: Operator Parser (UnionM SymbExpr)
opBetterHole = InfixL $ do
  ops <- oplst
  genSymSimpleIndexed @SymBool ops

-- hole op is handled separately
operatorTable :: [[Operator Parser (UnionM SymbExpr)]]
operatorTable =
  [ [binary "*" (\a b -> mrgSingle $ SMulExpr a b)],
    [ binary "+" (\a b -> mrgSingle $ SAddExpr a b),
      binary "-" (\a b -> mrgSingle $ SSubExpr a b)
    ],
    [ opHoleOperator,
      opBetterHole
    ]
  ]

expr :: Parser (UnionM SymbExpr)
expr = makeExprParser exprInner operatorTable

exprInner :: Parser (UnionM SymbExpr)
exprInner = choice [parens expr, concIntExpr, intHoleExpr, intHoleRangeExpr]

exprWholeString :: Parser (UnionM SymbExpr)
exprWholeString = do
  e <- lexeme expr
  eof
  return e

getSketch :: B.ByteString -> String -> UnionM SymbExpr
getSketch code name = case runSymGenIndexed (runParserT exprWholeString "a" code) name of
  Left i -> error $ errorBundlePretty i
  Right i -> i