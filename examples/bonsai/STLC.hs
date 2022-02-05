{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module STLC where

import BonsaiTree
import Control.Monad.Except
import qualified Data.ByteString as B
import Data.Maybe
import Data.MemoTrie
import Error
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Match
import Pattern
import SyntaxSpec
import MatchSyntax
import Control.DeepSeq
import Env
-- import Debug.Trace

stlcSyntax :: OptimSyntaxSpec 14
stlcSyntax =
  buildSyntax
    [ "term"
        --> [ ("lambda" -* ("name" -* "type")) -* "term",
              "call" -* ("term" -* "term"),
              "one",
              "nil",
              "cons",
              "hd",
              "tl",
              "+",
              "name"
            ],
      "type" --> ["int", "listof" -* "int", "arrow" -* ("type" -* "type")],
      "name" --> ["a", "b", "c"]
    ]

simpleNode :: B.ByteString -> BonsaiTree 14
simpleNode = unsafeLeaf stlcSyntax

oneNode :: BonsaiTree 14
oneNode = simpleNode "one"

nilNode :: BonsaiTree 14
nilNode = simpleNode "nil"

pairNode :: BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
pairNode l r = BonsaiNode (mrgSingle l) (mrgSingle r)

callNode :: BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
callNode l r = pairNode (simpleNode "call") $ pairNode l r

lambdaNode :: B.ByteString -> BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
lambdaNode name ty =
  pairNode
    ( pairNode
        (simpleNode "lambda")
        ( pairNode
            (simpleNode name)
            ty
        )
    )

uopNode :: B.ByteString -> BonsaiTree 14 -> BonsaiTree 14
uopNode name = callNode (simpleNode name)

bopNode :: B.ByteString -> BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
bopNode name l = callNode (callNode (unsafeLeaf stlcSyntax name) l)

consNode :: BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
consNode = bopNode "cons"

hdNode :: BonsaiTree 14 -> BonsaiTree 14
hdNode = uopNode "hd"

tlNode :: BonsaiTree 14 -> BonsaiTree 14
tlNode = uopNode "tl"

plusNode :: BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
plusNode = bopNode "+"

intTy :: BonsaiTree 14
intTy = simpleNode "int"

listOfIntTy :: BonsaiTree 14
listOfIntTy = pairNode (simpleNode "listof") intTy

arrowTy :: BonsaiTree 14 -> BonsaiTree 14 -> BonsaiTree 14
arrowTy arg res = pairNode (simpleNode "arrow") (pairNode arg res)

arrowTyU :: UnionM (BonsaiTree 14) -> BonsaiTree 14 -> BonsaiTree 14
arrowTyU arg res = pairNode (simpleNode "arrow") (BonsaiNode arg (mrgSingle res))

availableNames :: [BonsaiTree 14]
availableNames = [simpleNode "a", simpleNode "b", simpleNode "c"]

isAvailableNameNode :: BonsaiTree 14 -> SymBool
isAvailableNameNode node = foldl (\acc v -> node ==~ v ||~ acc) (conc False) availableNames

asLeaf :: BonsaiError -> BonsaiTree 14 -> ExceptT BonsaiError UnionM (BonsaiTree 14)
asLeaf _ x@(BonsaiLeaf _) = mrgReturn x
asLeaf e _ = throwError e

asNode :: BonsaiError -> BonsaiTree 14 -> ExceptT BonsaiError UnionM (BonsaiTree 14)
asNode _ x@(BonsaiNode _ _) = mrgReturn x
asNode e _ = throwError e

typer' :: BonsaiTree 14 -> Env 14 (BonsaiTree 14) -> ExceptT BonsaiError UnionM (BonsaiTree 14)
typer' = memo2 $ \tree env -> {-trace (show tree) $ trace (show env) $-}
  bonsaiMatchCustomError
    BonsaiTypeError
    stlcSyntax
    [ literal "one" ==> mrgReturn intTy,
      literal "nil" ==> mrgReturn listOfIntTy,
      literal "cons" ==> mrgReturn (arrowTy intTy (arrowTy listOfIntTy listOfIntTy)),
      literal "hd" ==> mrgReturn (arrowTy listOfIntTy intTy),
      literal "tl" ==> mrgReturn (arrowTy listOfIntTy listOfIntTy),
      literal "+" ==> mrgReturn (arrowTy intTy (arrowTy intTy intTy)),
      ((literal "lambda" *= (placeHolder *= placeHolder)) *= placeHolder)
        ==> ( \name ty expr -> do
                n <- lift name
                _ <- gassertWithError BonsaiTypeError (isAvailableNameNode n)
                let BonsaiLeaf sym = n -- will never call fail because we have partial evaluation
                res <- typer' #~ expr # envAdd env sym ty
                mrgReturn $ arrowTyU ty res
            ),
      (literal "call" *= (placeHolder *= placeHolder))
        ==> ( \func arg -> do
                tres <- typer' #~ func # env
                case tres of
                  BonsaiNode _ body -> do
                    bres <- lift body
                    case bres of
                      BonsaiNode funcArgTy funcResTy -> do
                        argTy <- typer' #~ arg # env
                        funcArgTy1 <- lift funcArgTy
                        _ <- gassertWithError BonsaiTypeError (argTy ==~ funcArgTy1)
                        mrgLift funcResTy
                      _ -> throwError BonsaiTypeError
                  _ -> throwError BonsaiTypeError
            ),
      placeHolder
        ==> ( \v -> do
                s <- lift v
                case s of
                  BonsaiLeaf sym -> do
                    _ <- envResolve BonsaiTypeError env sym
                    mrgReturn intTy

                  _ -> throwError BonsaiTypeError
            )
    ]
    tree

typer :: BonsaiTree 14 -> ExceptT BonsaiError UnionM (BonsaiTree 14)
typer tree = typer' tree (mrgSingle [])

data STLCValue
  = STLCInt SymInteger
  | STLCList (UnionM [SymInteger])
  | STLCBuiltin (SymUnsignedBV 14)
  | STLCPartiallyAppliedBuiltin (SymUnsignedBV 14) (UnionM STLCValue)
  | STLCLambda (SymUnsignedBV 14) (UnionM (BonsaiTree 14)) (Env 14 STLCValue)
  deriving (Show, Eq, Generic, Mergeable SymBool, NFData)

instance HasTrie STLCValue where
  newtype STLCValue :->: x = STLCValueTrie {unSTLCValueTrie :: Reg STLCValue :->: x}
  trie = trieGeneric STLCValueTrie
  untrie = untrieGeneric unSTLCValueTrie
  enumerate = enumerateGeneric unSTLCValueTrie

$(makeUnionMWrapper "u" ''STLCValue)

applyBuiltin :: STLCValue -> UnionM STLCValue -> ExceptT BonsaiError UnionM STLCValue
applyBuiltin (STLCBuiltin v) arg =
  mrgGuard
    (Just v ==~ (conc <$> terminalToBV stlcSyntax "hd"))
    ( do
        a <- lift arg
        case a of
          STLCList lv -> do
            listv <- lift lv
            case listv of
              [] -> uSTLCInt 1
              (hd : _) -> uSTLCInt hd
          _ -> throwError BonsaiExecError
    )
    ( mrgGuard
        (Just v ==~ (conc <$> terminalToBV stlcSyntax "tl"))
        ( do
            a <- lift arg
            case a of
              STLCList lv -> do
                listv <- lift lv
                case listv of
                  [] -> uSTLCList (mrgSingle [])
                  (_ : tl) -> uSTLCList (mrgSingle tl)
              _ -> throwError BonsaiExecError
        )
        (uSTLCPartiallyAppliedBuiltin v arg)
    )
applyBuiltin (STLCPartiallyAppliedBuiltin v arg1) arg2 =
  mrgGuard
    (Just v ==~ (conc <$> terminalToBV stlcSyntax "+"))
    ( do
        a <- lift arg1
        b <- lift arg2
        case (a, b) of
          (STLCInt a1, STLCInt a2) -> uSTLCInt $ a1 + a2
          _ -> throwError BonsaiExecError
    )
    ( mrgGuard
        (Just v ==~ (conc <$> terminalToBV stlcSyntax "cons"))
        ( do
            a <- lift arg1
            b <- lift arg2
            case (a, b) of
              (STLCInt a1, STLCList a2) -> uSTLCList $ mrgFmap (a1 :) a2
              _ -> throwError BonsaiExecError
        )
        (throwError BonsaiExecError)
    )
applyBuiltin _ _ = throwError BonsaiExecError

interpreter' :: BonsaiTree 14 -> Env 14 STLCValue -> Int -> ExceptT BonsaiError UnionM STLCValue
interpreter' = memo3 $ \tree env reccount -> {-trace (show tree) $ trace (show env) $ trace (show reccount) $-}
  if reccount >= 2
    then throwError BonsaiRecursionError
    else
      bonsaiMatchCustomError
        BonsaiExecError
        stlcSyntax
        [ literal "one" ==> uSTLCInt 1,
          literal "nil" ==> uSTLCList (mrgSingle []),
          literal "hd" ==> uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "hd"))),
          literal "tl" ==> uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "tl"))),
          literal "cons" ==> uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "cons"))),
          literal "+" ==> uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "+"))),
          ((literal "lambda" *= (placeHolder *= placeHolder)) *= placeHolder)
            ==> ( \name _ expr -> do
                    l <- lift name
                    gassertWithError BonsaiExecError (isAvailableNameNode l)
                    let BonsaiLeaf sym = l
                    uSTLCLambda sym expr env
                ),
          (literal "call" *= (placeHolder *= placeHolder))
            ==> ( \func arg -> do
              argv <- mrgFmap (mrgSingle @SymBool) $ interpreter' #~ arg # env # reccount
              funcv <- interpreter' #~ func # env # reccount
              case funcv of
                f@STLCBuiltin {} -> applyBuiltin f argv
                f@STLCPartiallyAppliedBuiltin {} -> applyBuiltin f argv
                STLCLambda name expr env1 -> interpreter' #~ expr # envAdd env1 name argv # (reccount + 1)
                _ -> throwError BonsaiExecError
                ),
          placeHolder ==> (\v -> do
            s <- lift v
            case s of
              BonsaiLeaf sym -> envResolve BonsaiExecError env sym
              _ -> throwError BonsaiExecError
            )
        ]
        tree

interpreter :: BonsaiTree 14 -> ExceptT BonsaiError UnionM STLCValue
interpreter tree = interpreter' tree (mrgSingle []) 0

matchStlcSyntax :: BonsaiTree 14 -> B.ByteString -> SymBool
matchStlcSyntax = matchSyntax stlcSyntax matchStlcRule

matchStlcRule :: Rule -> BonsaiTree 14 -> SymBool
matchStlcRule = matchRule stlcSyntax matchStlcSyntax matchStlcRule

execStlc :: BonsaiTree 14 -> ExceptT BonsaiError UnionM STLCValue
execStlc tree = do
  gassertWithError BonsaiTypeError (matchStlcSyntax tree "term")
  mrgFmap (const ()) $ typer tree
  interpreter tree

