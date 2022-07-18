{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Monad.Combinators.Expr
import qualified Data.ByteString as B
import Data.Proxy
import Data.Void
import Expr
import Grisette
import Grisette.Lib.Text.Megaparsec ()
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Text.Megaparsec.Byte.Lexer as L

type Parser = ParsecT Void B.ByteString GenSymFresh

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: B.ByteString -> Parser B.ByteString
symbol = L.symbol space

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

concIntExpr :: Parser (UnionM SymbExpr)
concIntExpr = uSConstantExpr <$> lexeme L.decimal

intlst :: Parser [Integer]
intlst = between (symbol "??[") (symbol "]") (sepBy1 L.decimal (symbol ","))

intHoleRangeExpr :: Parser (UnionM SymbExpr)
intHoleRangeExpr = do
  l <- intlst
  (i :: UnionM SymInteger) <- choose (conc <$> l)
  return $ uSConstantExpr $ getSingle i

intHoleExpr :: Parser (UnionM SymbExpr)
intHoleExpr = do
  _ <- symbol "??i"
  i <- genSymSimpleFresh (Proxy :: Proxy SymBool) ()
  return $ uSConstantExpr i

binary :: B.ByteString -> (a -> a -> a) -> Operator Parser a
binary nm f = InfixL (f <$ symbol nm)

opHoleOperator :: Operator Parser (UnionM SymbExpr)
opHoleOperator = InfixL $ do
  _ <- symbol "??op"
  simpleChoose (Proxy :: Proxy SymBool) [uSAddExpr, uSSubExpr, uSMulExpr]

addOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
addOp = symbol "+" >> return uSAddExpr

subOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
subOp = symbol "-" >> return uSSubExpr

mulOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
mulOp = symbol "*" >> return uSMulExpr

oplst :: Parser [UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr]
oplst = between (symbol "??{") (symbol "}") (sepBy (choice [addOp, subOp, mulOp]) (symbol ","))

opBetterHole :: Operator Parser (UnionM SymbExpr)
opBetterHole = InfixL $ do
  ops <- oplst
  simpleChoose (Proxy :: Proxy SymBool) ops

-- hole op is handled separately
operatorTable :: [[Operator Parser (UnionM SymbExpr)]]
operatorTable =
  [ [binary "*" uSMulExpr],
    [ binary "+" uSAddExpr,
      binary "-" uSSubExpr
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

getSketch :: B.ByteString -> GenSymIdent -> UnionM SymbExpr
getSketch code nm = case runGenSymFresh (runParserT exprWholeString "a" code) nm of
  Left i -> error $ errorBundlePretty i
  Right i -> i
