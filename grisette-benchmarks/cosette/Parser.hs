{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Monad.Combinators.Expr
import qualified Data.ByteString as B
import Data.ByteString.Internal
import Data.Void
import Syntax
import Text.Megaparsec
import Text.Megaparsec.Byte
import qualified Text.Megaparsec.Byte.Lexer as L

type Parser = Parsec Void B.ByteString

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: B.ByteString -> Parser B.ByteString
symbol = L.symbol space

lparen :: Parser B.ByteString
lparen = symbol "("

rparen :: Parser B.ByteString
rparen = symbol ")"

parens :: Parser a -> Parser a
parens = between lparen rparen

rword :: B.ByteString -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

rwordList :: [B.ByteString]
rwordList = ["NAMED", "JOIN", "AS", "SELECT", "WHERE", "FROM", "NULL", "LEFT-OUTER-JOIN2", "LEFT-OUTER-JOIN"]

ident :: Parser B.ByteString
ident = (lexeme . try) (p >>= check)
  where
    idtail = many (try alphaNumChar <|> char (c2w '\''))
    p = B.pack <$> ((:) <$> lowerChar <*> idtail)
    check s =
      if s `elem` rwordList
        then fail $ "keyword " ++ show s ++ "cannot be an identifier"
        else return s

rawname :: Parser B.ByteString
rawname = (lexeme . try) (p >>= check)
  where
    idtail = many (try alphaNumChar <|> char (c2w '.'))
    p = B.pack <$> ((:) <$> letterChar <*> idtail)
    check s =
      if s `elem` rwordList
        then fail $ "keyword " ++ show s ++ "cannot be an rawname"
        else return s

rawnamelst :: Parser [B.ByteString]
rawnamelst = between (symbol "[") (symbol "]") (sepBy rawname (symbol ","))

wholeStringQuery :: Parser Query
wholeStringQuery = do
  q <- query
  eof
  return q

query :: Parser Query
query =
  space
    >> ( try namedQuery
           <|> try joinQuery
           <|> try asQuery
           <|> try selectQuery
           <|> try leftOuterJoinQuery
           <|> try leftOuterJoin2Query
           <|> subQuery
       )

subQuery :: Parser Query
subQuery = QuerySub <$> between (symbol "${") (symbol "}") ident

namedQuery :: Parser Query
namedQuery = do
  _ <- rword "NAMED"
  QueryNamed <$> ident

joinQuery :: Parser Query
joinQuery = do
  _ <- rword "JOIN"
  q1 <- parens query
  QueryJoin q1 <$> parens query

asQuery :: Parser Query
asQuery = do
  _ <- rword "AS"
  q <- parens query
  try (asQueryFull q) <|> asQuerySimple q

asQueryFull :: Query -> Parser Query
asQueryFull q = do
  s <- rawname
  QueryRenameFull q s <$> rawnamelst

asQuerySimple :: Query -> Parser Query
asQuerySimple q = QueryRename q <$> rawname

selectQuery :: Parser Query
selectQuery = do
  _ <- rword "SELECT"
  idents <- some rawname
  _ <- rword "FROM"
  q <- parens query
  _ <- rword "WHERE"
  QuerySelect idents q <$> filterExpr

leftOuterJoin2Query :: Parser Query
leftOuterJoin2Query = do
  _ <- rword "LEFT-OUTER-JOIN2"
  q1 <- parens query
  q2 <- parens query
  QueryLeftOuterJoin2 q1 q2 <$> parens query

leftOuterJoinQuery :: Parser Query
leftOuterJoinQuery = do
  _ <- rword "LEFT-OUTER-JOIN"
  q1 <- parens query
  q2 <- parens query
  i1 <- lexeme L.decimal
  QueryLeftOuterJoin q1 q2 i1 <$> lexeme L.decimal

operatorTable :: [[Operator Parser Filter]]
operatorTable =
  [ [prefix "NOT" FilterNot],
    [binary "AND" FilterConj],
    [binary "OR" FilterDisj]
  ]

prefix :: ByteString -> (a -> a) -> Operator Parser a
prefix name f = Prefix (f <$ symbol name)

binary :: ByteString -> (a -> a -> a) -> Operator Parser a
binary name f = InfixL (f <$ symbol name)

filterTrue :: Parser Filter
filterTrue = do
  _ <- rword "TRUE"
  return FilterTrue

filterFalse :: Parser Filter
filterFalse = do
  _ <- rword "False"
  return FilterFalse

filterEq :: Val -> Parser Filter
filterEq v = do
  _ <- symbol "="
  FilterBinOp FBinEq v <$> valueParser

filterNEq :: Val -> Parser Filter
filterNEq v = do
  _ <- symbol "<>"
  FilterBinOp FBinNEq v <$> valueParser

filterBinOp :: Parser Filter
filterBinOp = do
  v1 <- valueParser
  try (filterEq v1) <|> filterNEq v1

filterTerm :: Parser Filter
filterTerm = parens filterExpr <|> filterTrue <|> filterFalse <|> filterBinOp

filterExpr :: Parser Filter
filterExpr = makeExprParser filterTerm operatorTable

valueNull :: Parser Val
valueNull = do
  _ <- rword "NULL"
  return $ ValConst Nothing

valueInt :: Parser Val
valueInt = ValConst . Just <$> lexeme L.decimal

valueName :: Parser Val
valueName = ValColumnRef <$> rawname

valueParser :: Parser Val
valueParser = try valueNull <|> try valueInt <|> valueName
