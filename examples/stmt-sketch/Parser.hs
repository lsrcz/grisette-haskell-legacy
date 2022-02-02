{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Parser where

import Control.Monad.Combinators.Expr as E
import Control.Monad.State as ST
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Void
import DataStructures
import Grisette.Core
import Grisette.SymPrim.Term
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
concIntExpr = uSIntConstantExpr <$> lexeme L.decimal

intlst :: Parser [Integer]
intlst = between (symbol "??[") (symbol "]") (sepBy1 L.decimal (symbol ","))

intHoleRangeExpr :: Parser (UnionM SymbExpr)
intHoleRangeExpr = do
  l <- intlst
  let x = conc @SymInteger <$> l
  i <- choose @SymBool (head x) (tail x)
  return $ uSIntConstantExpr $ getSingle i

intHoleExpr :: Parser (UnionM SymbExpr)
intHoleExpr = do
  _ <- symbol "??i"
  i <- genSymSimpleIndexed @SymBool ()
  return $ uSIntConstantExpr i

boolHoleExpr :: Parser (UnionM SymbExpr)
boolHoleExpr = do
  _ <- symbol "??b"
  b <- genSymSimpleIndexed @SymBool ()
  return $ uSBoolConstantExpr b

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
identExpr = uSVarExpr <$> ident

binary :: B.ByteString -> (a -> a -> a) -> Operator Parser a
binary name f = E.InfixL (f <$ symbol name)

opHoleOperator :: Operator Parser (UnionM SymbExpr)
opHoleOperator = E.InfixL $ do
  _ <- symbol "??op"
  simpleChoose @SymBool uSAddExpr [uSSubExpr, uSMulExpr, uSLtExpr,
    uSEqExpr, uSAndExpr, uSOrExpr]

addOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
addOp = symbol "+" >> return uSAddExpr

subOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
subOp = symbol "-" >> return uSSubExpr

mulOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
mulOp = symbol "*" >> return uSMulExpr

ltOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
ltOp = symbol "<" >> return uSLtExpr

eqOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
eqOp = symbol "==" >> return uSEqExpr

andOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
andOp = symbol "&&" >> return uSAndExpr

orOp :: Parser (UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr)
orOp = symbol "||" >> return uSOrExpr

oplst :: Parser [UnionM SymbExpr -> UnionM SymbExpr -> UnionM SymbExpr]
oplst =
  between (symbol "??{") (symbol "}") $
    sepBy (choice [addOp, subOp, mulOp, ltOp, eqOp, andOp, orOp]) (symbol ",")

opBetterHole :: Operator Parser (UnionM SymbExpr)
opBetterHole = E.InfixL $ do
  ops <- between (symbol "??{") (symbol "}") $
    sepBy (choice [addOp, subOp, mulOp, ltOp, eqOp, andOp, orOp]) (symbol ",")
  simpleChoose @SymBool (head ops) (tail ops)

-- hole op is handled separately
operatorTable :: [[Operator Parser (UnionM SymbExpr)]]
operatorTable =
  [ [binary "*" uSMulExpr],
    [ binary "+" uSAddExpr,
      binary "-" uSSubExpr
    ],
    [ binary "<" uSLtExpr,
      binary "==" uSEqExpr
    ],
    [ binary "&&" uSAndExpr
    ],
    [ binary "||" uSOrExpr
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
