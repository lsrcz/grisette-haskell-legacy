{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Parser where

import Control.Monad.Combinators.Expr as E
import Control.Monad.State as ST
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Void
import DataStructures
import Grisette.Control.Monad.UnionM
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymGen
import Grisette.Data.SymPrim
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Text.Megaparsec.Byte.Lexer as L

type Parser = ParsecT Void B.ByteString (ST.State SymGenState)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: B.ByteString -> Parser B.ByteString
symbol = L.symbol space

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

concIntExpr :: Parser (UnionM SymbExpr)
concIntExpr = mrgSingle . SIntConstantExpr <$> lexeme L.decimal

intlst :: Parser [Integer]
intlst = between (symbol "??[") (symbol "]") (sepBy1 L.decimal (symbol ","))

intHoleRangeExpr :: Parser (UnionM SymbExpr)
intHoleRangeExpr = do
  l <- intlst
  let x = conc @SymInteger <$> l
  i <- choose @SymBool (head x) (tail x)
  return $ mrgSingle $ SIntConstantExpr $ getSingle i

intHoleExpr :: Parser (UnionM SymbExpr)
intHoleExpr = do
  _ <- symbol "??i"
  i <- genSymSimpleIndexed @SymBool ()
  return $ mrgSingle $ SIntConstantExpr i

boolHoleExpr :: Parser (UnionM SymbExpr)
boolHoleExpr = do
  _ <- symbol "??b"
  b <- genSymSimpleIndexed @SymBool ()
  return $ mrgSingle $ SBoolConstantExpr b

identHole :: Parser SIdentifier
identHole = do
  _ <- symbol "??v"
  genSymSimpleIndexed @SymBool ()

concIdent :: Parser SIdentifier
concIdent = do
  _ <- symbol "v"
  SIdentifier <$> L.decimal

ident :: Parser SIdentifier
ident = lexeme $ choice [identHole, concIdent]

identExpr :: Parser (UnionM SymbExpr)
identExpr = mrgSingle . SVarExpr <$> ident

binary :: B.ByteString -> (a -> a -> a) -> Operator Parser a
binary name f = E.InfixL (f <$ symbol name)

opHoleOperator :: Operator Parser (UnionM SymbExpr)
opHoleOperator = E.InfixL $ do
  _ <- symbol "??op"
  genSymSimpleIndexed @SymBool [Add, Sub, Mul]

addOp :: Parser Op
addOp = symbol "+" >> return Add

subOp :: Parser Op
subOp = symbol "-" >> return Sub

mulOp :: Parser Op
mulOp = symbol "*" >> return Mul

ltOp :: Parser Op
ltOp = symbol "<" >> return Lt

eqOp :: Parser Op
eqOp = symbol "==" >> return Eq

andOp :: Parser Op
andOp = symbol "&&" >> return And

orOp :: Parser Op
orOp = symbol "||" >> return Or

oplst :: Parser [Op]
oplst =
  between (symbol "??{") (symbol "}") $
    sepBy (choice [addOp, subOp, mulOp, ltOp, eqOp, andOp, orOp]) (symbol ",")

opBetterHole :: Operator Parser (UnionM SymbExpr)
opBetterHole = E.InfixL $ do
  ops <- oplst
  genSymSimpleIndexed @SymBool ops

-- hole op is handled separately
operatorTable :: [[Operator Parser (UnionM SymbExpr)]]
operatorTable =
  [ [binary "*" (\a b -> mrgSingle $ SMulExpr a b)],
    [ binary "+" (\a b -> mrgSingle $ SAddExpr a b),
      binary "-" (\a b -> mrgSingle $ SSubExpr a b)
    ],
    [ binary "<" (\a b -> mrgSingle $ SLtExpr a b),
      binary "==" (\a b -> mrgSingle $ SEqExpr a b)
    ],
    [ binary "&&" (\a b -> mrgSingle $ SAndExpr a b)
    ],
    [ binary "||" (\a b -> mrgSingle $ SOrExpr a b)
    ],
    [ opHoleOperator,
      opBetterHole
    ]
  ]

expr :: Parser (UnionM SymbExpr)
expr = makeExprParser exprInner operatorTable

exprInner :: Parser (UnionM SymbExpr)
exprInner =
  choice $
    try
      <$> [ parens expr,
            concIntExpr,
            intHoleExpr,
            intHoleRangeExpr,
            boolHoleExpr,
            identExpr
          ]

exprWholeString :: Parser (UnionM SymbExpr)
exprWholeString = do
  e <- lexeme expr
  eof
  return e

assignStmt :: Parser SymbStmt
assignStmt = do
  i <- ident
  _ <- symbol "="
  SAssignStmt i <$> expr

assertStmt :: Parser SymbStmt
assertStmt = do
  _ <- symbol "assert"
  SAssertStmt <$> expr

ifStmt :: Parser SymbStmt
ifStmt = do
  _ <- symbol "if"
  cond <- parens expr
  l <- stmtBlock
  _ <- symbol "else"
  SIfStmt cond l <$> stmtBlock

stmt :: Parser SymbStmt
stmt = choice $ try <$> [ifStmt, assignStmt, assertStmt]

stmtSeq :: Parser [SymbStmt]
stmtSeq = sepBy (try stmt) (symbol ";")

stmtBlock :: Parser [SymbStmt]
stmtBlock = between (symbol "{") (symbol "}") stmtSeq

program :: Parser SymbProgram
program = do
  _ <- space
  s <- stmtSeq
  eof
  return $ SymbProgram s

getSketch :: B.ByteString -> String -> SymbProgram
getSketch code name = case runSymGenIndexed (runParserT program "a" code) name of
  Left i -> error $ errorBundlePretty i
  Right i -> i

sketch :: QuasiQuoter
sketch =
  QuasiQuoter
    { quoteExp = compile . C.pack,
      quotePat = notHandled "patterns",
      quoteType = notHandled "types",
      quoteDec = notHandled "declarations"
    }
  where
    notHandled things =
      error $ things ++ " are not handled by the cosette quasiquoter"

compile :: B.ByteString -> Q Exp
compile s = case runSymGenIndexed (runParserT program "input" $ B.tail y) (C.unpack n) of
  Left peb -> fail $ errorBundlePretty peb
  Right qu ->
    [|qu|]
  where
    (n, y) = C.break (== ':') s
