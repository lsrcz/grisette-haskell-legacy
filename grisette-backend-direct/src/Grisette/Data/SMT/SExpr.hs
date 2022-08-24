{-# LANGUAGE OverloadedStrings #-}

module Grisette.Data.SMT.SExpr
  ( SExpr (..),
    sexprByteString,
    sexprByteStringBuilder,
    symbol,
    intSort,
    boolSort,
    SMTLogic (..),
    setLogic,
    defineFun,
    checkSat,
    getModel,
    trueLit,
    falseLit,
    boolLit,
    Grisette.Data.SMT.SExpr.not,
    Grisette.Data.SMT.SExpr.and,
    andMany,
    Grisette.Data.SMT.SExpr.or,
    orMany,
  )
where

import ByteString.StrictBuilder
-- import qualified Data.ByteString as B

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.List

data SExpr = Atom Builder | List [SExpr] Builder

sexprByteStringBuilder :: SExpr -> Builder
sexprByteStringBuilder (Atom v) = v
sexprByteStringBuilder (List _ r) = r

sexprByteString :: SExpr -> B.ByteString
sexprByteString = builderBytes . sexprByteStringBuilder

instance Show SExpr where
  show = C.unpack . builderBytes . sexprByteStringBuilder

space :: Builder
space = " "

{-# INLINE list #-}
list :: [SExpr] -> SExpr
list [] = List [] "()"
list l@(hd : sub) =
  List l $
    "("
      <> foldl' (\acc v -> acc <> space <> sexprByteStringBuilder v) (sexprByteStringBuilder hd) sub
      <> ")"

{-# INLINE apply #-}
apply :: SExpr -> [SExpr] -> SExpr
apply hd tl = list $ hd : tl

{-# INLINE unary #-}
unary :: SExpr -> SExpr -> SExpr
unary op x = apply op [x]

{-# INLINE binary #-}
binary :: SExpr -> SExpr -> SExpr -> SExpr
binary op x y = apply op [x, y]

{-# INLINE ternary #-}
ternary :: SExpr -> SExpr -> SExpr -> SExpr -> SExpr
ternary op x y z = apply op [x, y, z]

data SMTLogic = ALL | QF_BV

qfbvAtom :: SExpr
qfbvAtom = Atom "QF_BV"

allAtom :: SExpr
allAtom = Atom "ALL"

logicAtom :: SMTLogic -> SExpr
logicAtom QF_BV = qfbvAtom
logicAtom ALL = allAtom

setLogicAtom :: SExpr
setLogicAtom = Atom "set-logic"

{-# INLINE setLogic #-}
setLogic :: SMTLogic -> SExpr
setLogic = unary setLogicAtom . logicAtom

{-# INLINE sortedSymbol #-}
sortedSymbol :: B.ByteString -> SExpr -> SExpr
sortedSymbol symb typ = list [symbol symb, typ]

defineFunAtom :: SExpr
defineFunAtom = Atom "define-fun"

{-# INLINE defineFun #-}
defineFun ::
  -- | function name
  B.ByteString ->
  -- | function parameters with sorts
  [(B.ByteString, SExpr)] ->
  -- | Result sort
  SExpr ->
  -- | Definition
  SExpr ->
  SExpr
defineFun name param resTyp def = list [defineFunAtom, symbol name, list $ uncurry sortedSymbol <$> param, resTyp, def]

checkSat :: SExpr
checkSat = list [Atom "check-sat"]

getModel :: SExpr
getModel = list [Atom "get-model"]

boolSort :: SExpr
boolSort = Atom "Bool"

intSort :: SExpr
intSort = Atom "Int"

trueLit :: SExpr
trueLit = Atom "true"

falseLit :: SExpr
falseLit = Atom "false"

boolLit :: Bool -> SExpr
boolLit True = trueLit
boolLit False = falseLit

notAtom :: SExpr
notAtom = Atom "not"

andAtom :: SExpr
andAtom = Atom "and"

orAtom :: SExpr
orAtom = Atom "or"

{-# INLINE not #-}
not :: SExpr -> SExpr
not = unary notAtom

{-# INLINE and #-}
and :: SExpr -> SExpr -> SExpr
and = binary andAtom

{-# INLINE andMany #-}
andMany :: [SExpr] -> SExpr
andMany = apply andAtom

{-# INLINE or #-}
or :: SExpr -> SExpr -> SExpr
or = binary orAtom

{-# INLINE orMany #-}
orMany :: [SExpr] -> SExpr
orMany = apply orAtom

symbol :: B.ByteString -> SExpr
symbol = Atom . bytes
