{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module STLC (stlcSyntax, STLCTree, ConcSTLCTree, execStlc) where

import Bonsai.BonsaiTree
import Bonsai.Env
import Bonsai.Match
import Bonsai.MatchSyntaxNoMemo
import Bonsai.Pattern
import Bonsai.SyntaxSpec
import Control.DeepSeq
import Control.Monad.Except
import qualified Data.ByteString as B
import Data.Hashable
import Data.Maybe
import GHC.Generics
import Grisette
import Grisette.Unordered.UUnionM

-- import Debug.Trace

type STLCBitWidth = 14

type STLCTree = BonsaiTree (SymWordN STLCBitWidth)

type ConcSTLCTree = ConcBonsaiTree (WordN STLCBitWidth)

stlcSyntax :: OptimSyntaxSpec STLCBitWidth
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

stlcLiteral :: B.ByteString -> Pattern (SymWordN STLCBitWidth) 0
stlcLiteral s = literal $ fromJust $ toSym $ terminalToBV stlcSyntax s

simpleNode :: B.ByteString -> STLCTree
simpleNode = unsafeLeaf stlcSyntax

pairNode :: STLCTree -> STLCTree -> STLCTree
pairNode l r = BonsaiNode (mrgReturn l) (mrgReturn r)

intTy :: STLCTree
intTy = simpleNode "int"

listOfIntTy :: STLCTree
listOfIntTy = pairNode (simpleNode "listof") intTy

arrowTy :: STLCTree -> STLCTree -> STLCTree
arrowTy arg res = pairNode (simpleNode "arrow") (pairNode arg res)

arrowTyU :: UUnionM STLCTree -> UUnionM STLCTree -> STLCTree
arrowTyU arg res = pairNode (simpleNode "arrow") (BonsaiNode arg res)

availableNames :: [STLCTree]
availableNames = [simpleNode "a", simpleNode "b", simpleNode "c"]

isAvailableNameNode :: STLCTree -> SymBool
isAvailableNameNode node = foldl (\acc v -> node ==~ v ||~ acc) (conc False) availableNames

typer' :: STLCTree -> Env 14 STLCTree -> ExceptT BonsaiError UUnionM (UUnionM STLCTree)
typer' tree env =
  bonsaiMatchCustomError
    BonsaiTypeError
    [ stlcLiteral "one" ==> mrgReturn (mrgReturn intTy),
      stlcLiteral "nil" ==> mrgReturn (mrgReturn listOfIntTy),
      stlcLiteral "cons" ==> mrgReturn (mrgReturn (arrowTy intTy (arrowTy listOfIntTy listOfIntTy))),
      stlcLiteral "hd" ==> mrgReturn (mrgReturn (arrowTy listOfIntTy intTy)),
      stlcLiteral "tl" ==> mrgReturn (mrgReturn (arrowTy listOfIntTy listOfIntTy)),
      stlcLiteral "+" ==> mrgReturn (mrgReturn (arrowTy intTy (arrowTy intTy intTy))),
      ((stlcLiteral "lambda" *= (placeHolder *= placeHolder)) *= placeHolder)
        ==> ( \nm ty expr -> do
                n <- lift nm
                _ <- symFailIfNot BonsaiTypeError (isAvailableNameNode n)
                let BonsaiLeaf sym = n -- will never call fail because we have partial evaluation
                res <- typer' #~ expr # envAdd env sym ty
                mrgReturn $ mrgReturn $ arrowTyU ty res
            ),
      (stlcLiteral "call" *= (placeHolder *= placeHolder))
        ==> ( \func arg -> do
                tres <- typer' #~ func # env
                tresv <- lift tres
                case tresv of
                  BonsaiNode _ body -> do
                    bres <- lift body
                    case bres of
                      BonsaiNode funcArgTy funcResTy -> do
                        argTy <- typer' #~ arg # env
                        _ <- symFailIfNot BonsaiTypeError (argTy ==~ funcArgTy)
                        mrgReturn funcResTy
                      _ -> throwError BonsaiTypeError
                  _ -> throwError BonsaiTypeError
            ),
      placeHolder
        ==> ( \v -> do
                s <- lift v
                case s of
                  BonsaiLeaf sym -> do
                    _ <- envResolveU BonsaiTypeError env sym
                    mrgReturn . mrgReturn $ intTy
                  _ -> throwError BonsaiTypeError
            )
    ]
    tree

typer :: STLCTree -> ExceptT BonsaiError UUnionM (UUnionM STLCTree)
typer tree = typer' tree (mrgReturn [])

data STLCValue
  = STLCInt SymInteger
  | STLCList (UUnionM [SymInteger])
  | STLCBuiltin (SymWordN 14)
  | STLCPartiallyAppliedBuiltin (SymWordN 14) (UUnionM STLCValue)
  | STLCLambda (SymWordN 14) (UUnionM STLCTree) (Env 14 STLCValue)
  deriving (Show, Eq, Generic, NFData, Hashable)
  deriving (Mergeable SymBool) via (Default STLCValue)

$(makeUnionMWrapper "u" ''STLCValue)

applyBuiltin :: STLCValue -> UUnionM STLCValue -> ExceptT BonsaiError UUnionM (UUnionM STLCValue)
applyBuiltin (STLCBuiltin v) arg =
  mrgIf
    (Just v ==~ (conc <$> terminalToBV stlcSyntax "hd"))
    ( do
        a <- lift arg
        case a of
          STLCList lv -> do
            listv <- lift lv
            case listv of
              [] -> mrgReturn $ uSTLCInt 1
              (hd : _) -> mrgReturn $ uSTLCInt hd
          _ -> throwError BonsaiExecError
    )
    ( mrgIf
        (Just v ==~ (conc <$> terminalToBV stlcSyntax "tl"))
        ( do
            a <- lift arg
            case a of
              STLCList lv -> do
                listv <- lift lv
                case listv of
                  [] -> mrgReturn $ uSTLCList (mrgReturn [])
                  (_ : tl) -> mrgReturn $ uSTLCList (mrgReturn tl)
              _ -> throwError BonsaiExecError
        )
        (mrgReturn $ uSTLCPartiallyAppliedBuiltin v arg)
    )
applyBuiltin (STLCPartiallyAppliedBuiltin v arg1) arg2 =
  mrgIf
    (Just v ==~ (conc <$> terminalToBV stlcSyntax "+"))
    ( do
        a <- lift arg1
        b <- lift arg2
        case (a, b) of
          (STLCInt a1, STLCInt a2) -> mrgReturn $ uSTLCInt $ a1 + a2
          _ -> throwError BonsaiExecError
    )
    ( mrgIf
        (Just v ==~ (conc <$> terminalToBV stlcSyntax "cons"))
        ( do
            a <- lift arg1
            b <- lift arg2
            case (a, b) of
              (STLCInt a1, STLCList a2) -> mrgReturn $ uSTLCList $ mrgFmap (a1 :) a2
              _ -> throwError BonsaiExecError
        )
        (throwError BonsaiExecError)
    )
applyBuiltin _ _ = throwError BonsaiExecError

interpreter' :: STLCTree -> Env 14 STLCValue -> Int -> ExceptT BonsaiError UUnionM (UUnionM STLCValue)
interpreter' tree env reccount =
  if reccount >= 2
    then throwError BonsaiRecursionError
    else
      bonsaiMatchCustomError
        BonsaiExecError
        [ stlcLiteral "one" ==> mrgReturn (uSTLCInt 1),
          stlcLiteral "nil" ==> mrgReturn (uSTLCList (mrgReturn [])),
          stlcLiteral "hd" ==> mrgReturn (uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "hd")))),
          stlcLiteral "tl" ==> mrgReturn (uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "tl")))),
          stlcLiteral "cons" ==> mrgReturn (uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "cons")))),
          stlcLiteral "+" ==> mrgReturn (uSTLCBuiltin (conc (fromJust (terminalToBV stlcSyntax "+")))),
          ((stlcLiteral "lambda" *= (placeHolder *= placeHolder)) *= placeHolder)
            ==> ( \nm _ expr -> do
                    l <- lift nm
                    symFailIfNot BonsaiExecError (isAvailableNameNode l)
                    let BonsaiLeaf sym = l
                    mrgReturn (uSTLCLambda sym expr env)
                ),
          (stlcLiteral "call" *= (placeHolder *= placeHolder))
            ==> ( \func arg -> do
                    argv <- interpreter' #~ arg # env # reccount
                    funcv <- interpreter' #~ func # env # reccount
                    funcvv <- lift funcv
                    case funcvv of
                      f@STLCBuiltin {} -> applyBuiltin f argv
                      f@STLCPartiallyAppliedBuiltin {} -> applyBuiltin f argv
                      STLCLambda nm expr env1 -> interpreter' #~ expr # envAdd env1 nm argv # (reccount + 1)
                      _ -> throwError BonsaiExecError
                ),
          placeHolder
            ==> ( \v -> do
                    s <- lift v
                    case s of
                      BonsaiLeaf sym -> envResolveU BonsaiExecError env sym
                      _ -> throwError BonsaiExecError
                )
        ]
        tree

interpreter :: STLCTree -> ExceptT BonsaiError UUnionM (UUnionM STLCValue)
interpreter tree = interpreter' tree (mrgReturn []) 0

matchStlcSyntax :: STLCTree -> B.ByteString -> SymBool
matchStlcSyntax = matchSyntax stlcSyntax matchStlcRule

matchStlcRule :: Rule -> STLCTree -> SymBool
matchStlcRule = matchRule stlcSyntax matchStlcSyntax matchStlcRule

execStlc :: STLCTree -> ExceptT BonsaiError UUnionM (UUnionM STLCValue)
execStlc tree = do
  symFailIfNot BonsaiTypeError (matchStlcSyntax tree "term")
  mrgFmap (const ()) $ typer tree
  interpreter tree
