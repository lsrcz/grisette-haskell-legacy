{-# LANGUAGE OverloadedStrings #-}

module NanoScala (DotTree, ConcDotTree, dotSyntax, execDot) where

import Bonsai.BonsaiTree
import Bonsai.Env
import Bonsai.Match
import Bonsai.MatchSyntaxNoMemo
import Bonsai.Pattern
import Bonsai.SyntaxSpec
import Control.Monad.Except
import qualified Data.ByteString as B
import Data.Either.Combinators
import Data.Maybe
import Grisette
import Grisette.Unordered.UUnionM

type DotBitWidth = 15

type DotTree = BonsaiTree (SymWordN DotBitWidth)

type ConcDotTree = ConcBonsaiTree (WordN DotBitWidth)

dotSyntax :: OptimSyntaxSpec DotBitWidth
dotSyntax =
  buildSyntax
    [ "defn"
        --> [ "val" -* ("name" -* "term"),
              "typ" -* ("name" -* "type"),
              "and" -* ("defn" -* "defn")
            ],
      "term"
        --> [ "let" -* (("name" -* ("type" -* "type")) -* ("term" -* "term")),
              "defn",
              "var" -* "name",
              "null",
              "die" -* "term",
              "make-null" -* "type"
            ],
      "type"
        --> [ "Any",
              "Nothing",
              "get" -* ("term" -* "name"),
              "typ" -* ("name" -* "type"),
              "val" -* ("name" -* "type"),
              "and" -* ("type" -* "type"),
              "type" -* ("name" -* ("range" -* ("type" -* "type")))
            ],
      "name" --> ["a", "b", "c"]
    ]

dotLiteral :: B.ByteString -> Pattern (SymWordN DotBitWidth) 0
dotLiteral s = literal $ fromJust $ toSym $ terminalToBV dotSyntax s

eval' :: DotTree -> Env DotBitWidth DotResult -> ExceptT BonsaiError UUnionM (UUnionM DotResult)
eval' tree env =
  bonsaiMatchCustomError
    BonsaiExecError
    [ dotLiteral "let"
        *= ((placeHolder *= (placeHolder *= placeHolder)) *= (placeHolder *= placeHolder))
        ==> \nm _ _ value expr -> do
          v <- eval' #~ value # env
          env1 <- envAddTree BonsaiExecError env nm v
          eval' #~ expr # env1,
      dotLiteral "val" *= (placeHolder *= placeHolder) ==> \nm term -> do
        n <- extractName BonsaiExecError nm
        e <- eval' #~ term # env
        mrgReturn $ dotMakeU "value" n e,
      dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \_ _ -> mrgReturn $ uBonsaiLeaf $ uRight "empty",
      dotLiteral "and" *= (placeHolder *= placeHolder) ==> \a b -> do
        av <- eval' #~ a # env
        bv <- eval' #~ b # env
        mrgReturn $ dotJoinU av bv,
      dotLiteral "var" *= placeHolder ==> \nm -> do
        n <- extractName BonsaiExecError nm
        envResolveU BonsaiExecError env n,
      dotLiteral "die" *= placeHolder ==> \_ -> throwError BonsaiExecError,
      dotLiteral "make-null" *= placeHolder ==> \_ -> mrgReturn $ uBonsaiLeaf $ uRight "dummy1",
      dotLiteral "null" ==> mrgReturn (uBonsaiLeaf $ uRight "dummy2")
    ]
    tree

eval :: DotTree -> ExceptT BonsaiError UUnionM (UUnionM DotResult)
eval tree = eval' tree (mrgReturn [])

type DotT = UUnionM (Either (SymWordN DotBitWidth) B.ByteString)

type DotResult = BonsaiTree DotT

dotFindU :: B.ByteString -> SymWordN DotBitWidth -> UUnionM DotResult -> UUnionM (Maybe (UUnionM DotResult))
dotFindU kind nm tb = dotFind kind nm #~ tb

unsafeBV :: B.ByteString -> SymWordN DotBitWidth
unsafeBV s = fromJust $ toSym $ terminalToBV dotSyntax s

andBV :: SymWordN DotBitWidth
andBV = unsafeBV "and"

terminalLiteral :: B.ByteString -> Pattern DotT 0
terminalLiteral s = literal $ uLeft $ unsafeBV s

dotFind :: B.ByteString -> SymWordN DotBitWidth -> DotResult -> UUnionM (Maybe (UUnionM DotResult))
dotFind kind nm tb =
  mrgFmap (join . rightToMaybe) $
    runExceptT $
      bonsaiMatchCustomError
        BonsaiTypeError
        [ terminalLiteral "and" *= (placeHolder *= placeHolder) ==> \l r -> do
            lv <- lift $ dotFindU kind nm l
            case lv of
              Nothing -> do
                rv <- lift $ dotFindU kind nm r
                mrgReturn rv
              Just v -> uJust v,
          placeHolder *= placeHolder ==> \k v ->
            let e = uBonsaiNode (uBonsaiLeaf $ uRight kind) (uBonsaiLeaf $ uLeft nm)
             in mrgIf (e ==~ k) (uJust v) uNothing
        ]
        tb

dotMakeU :: B.ByteString -> SymWordN DotBitWidth -> UUnionM DotResult -> UUnionM DotResult
dotMakeU kind nm = uBonsaiNode (uBonsaiNode (uBonsaiLeaf $ uRight kind) (uBonsaiLeaf $ uLeft nm))

dotJoinU :: UUnionM DotResult -> UUnionM DotResult -> UUnionM DotResult
dotJoinU l r = uBonsaiNode (uBonsaiLeaf $ uLeft andBV) (uBonsaiNode l r)

uDotAny :: UUnionM DotResult
uDotAny = uBonsaiLeaf $ uLeft $ unsafeBV "Any"

uDotNothing :: UUnionM DotResult
uDotNothing = uBonsaiLeaf $ uLeft $ unsafeBV "Nothing"

uDotRange :: UUnionM DotResult -> UUnionM DotResult -> UUnionM DotResult
uDotRange ufrom uto = uBonsaiNode (uBonsaiLeaf $ uLeft $ unsafeBV "range") (uBonsaiNode ufrom uto)

reduceType ::
  Int ->
  Env DotBitWidth DotResult ->
  Bool ->
  DotTree ->
  ExceptT BonsaiError UUnionM (UUnionM DotResult)
reduceType reccount env strict tree =
  let reduceTypeR = reduceType (reccount + 1)
   in if reccount >= 3
        then throwError BonsaiTypeError
        else
          bonsaiMatchCustomError
            BonsaiTypeError
            [ dotLiteral "Any" ==> mrgReturn uDotAny,
              dotLiteral "Nothing" ==> mrgReturn uDotNothing,
              dotLiteral "and" *= (placeHolder *= placeHolder) ==> \a b ->
                if strict
                  then throwError BonsaiTypeError
                  else do
                    av <- reduceTypeR env True #~ a
                    bv <- reduceTypeR env True #~ b
                    mrgReturn $ dotJoinU av bv,
              dotLiteral "get" *= (placeHolder *= placeHolder) ==> \tbl nm -> do
                n <- extractName BonsaiTypeError nm
                t <- type' #~ tbl # env
                r <- lift $ dotFindU "type" n t
                case r of
                  Nothing -> throwError BonsaiTypeError
                  Just umb -> mrgReturn umb,
              dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \nm t -> do
                n <- extractName BonsaiTypeError nm
                t1 <- reduceTypeR env True #~ t
                return $ dotMakeU "type" n t1,
              dotLiteral "val" *= (placeHolder *= placeHolder) ==> \nm t -> do
                n <- extractName BonsaiTypeError nm
                t1 <- reduceTypeR env True #~ t
                return $ dotMakeU "value" n t1,
              dotLiteral "range" *= (placeHolder *= placeHolder) ==> \f t -> do
                tfrom <- reduceTypeR env True #~ f
                tto <- reduceTypeR env True #~ t
                return $ uDotRange tfrom tto
            ]
            tree

subType :: Int -> UUnionM DotResult -> UUnionM DotResult -> ExceptT BonsaiError UUnionM SymBool
subType reccount subv supv =
  let subTypeR = subType (reccount + 1)
   in if reccount >= 3
        then throwError BonsaiTypeError
        else
          bonsaiMatchCustomError
            BonsaiTypeError
            [ placeHolder *= terminalLiteral "Any" ==> \_ -> mrgReturn $ conc True,
              terminalLiteral "Nothing" *= placeHolder ==> \_ -> mrgReturn $ conc True,
              (terminalLiteral "and" *= (placeHolder *= placeHolder)) *= placeHolder ==> \l r sup -> do
                lv <- subTypeR l sup
                rv <- subTypeR r sup
                return $ lv ||~ rv,
              placeHolder *= (terminalLiteral "and" *= (placeHolder *= placeHolder)) ==> \sub l r -> do
                lv <- subTypeR sub l
                rv <- subTypeR sub r
                return $ lv ||~ rv,
              (terminalLiteral "range" *= (placeHolder *= placeHolder)) *= placeHolder ==> \_ upper r -> do
                subTypeR upper r,
              placeHolder *= (terminalLiteral "range" *= (placeHolder *= placeHolder)) ==> \l lower _ -> do
                subTypeR l lower,
              placeHolder ==> \_ -> mrgReturn $ subv ==~ supv
            ]
            (BonsaiNode subv supv)

type' :: DotTree -> Env DotBitWidth DotResult -> ExceptT BonsaiError UUnionM (UUnionM DotResult)
type' tree env =
  bonsaiMatchCustomError
    BonsaiTypeError
    [ dotLiteral "let"
        *= ((placeHolder *= (placeHolder *= placeHolder)) *= (placeHolder *= placeHolder))
        ==> \nm intype outtype value expr -> do
          it <- reduceType 0 env True #~ intype
          it' <- type' #~ value # env
          subi <- subType 0 it' it
          symFailIfNot BonsaiTypeError subi

          newenv <- envAddTree BonsaiTypeError env nm it

          ot <- reduceType 0 newenv True #~ outtype
          ot' <- type' #~ expr # newenv
          subo <- subType 0 ot' ot
          symFailIfNot BonsaiTypeError subo

          newenv' <- envAddTree BonsaiTypeError env nm it'
          reduceType 0 newenv' True #~ outtype,
      dotLiteral "val" *= (placeHolder *= placeHolder) ==> \nm term -> do
        n <- extractName BonsaiTypeError nm
        t <- type' #~ term # env
        return $ dotMakeU "value" n t,
      dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \nm term -> do
        n <- extractName BonsaiTypeError nm
        t <- type' #~ term # env
        return $ dotMakeU "type" n t,
      dotLiteral "and" *= (placeHolder *= placeHolder) ==> \_ _ -> throwError BonsaiTypeError,
      dotLiteral "var" *= placeHolder ==> \nm -> do
        n <- extractName BonsaiTypeError nm
        t <- envResolve' 3 BonsaiTypeError env n
        return $ mrgReturn t,
      dotLiteral "die" *= placeHolder ==> \expr -> do
        t <- type' #~ expr # env
        subt <- subType 0 t uDotNothing
        symFailIfNot BonsaiTypeError subt
        return t,
      dotLiteral "make-null" *= placeHolder ==> \t -> do
        t' <- reduceType 0 env False #~ t
        subt <- subType 0 t' uDotNothing
        symFailIfNot BonsaiTypeError (nots subt)
        return t',
      dotLiteral "null" ==> return uDotAny
    ]
    tree

typer :: DotTree -> ExceptT BonsaiError UUnionM (UUnionM DotResult)
typer tree = type' tree (mrgReturn [])

matchDotSyntax :: DotTree -> B.ByteString -> SymBool
matchDotSyntax = matchSyntax dotSyntax matchDotRule

matchDotRule :: Rule -> DotTree -> SymBool
matchDotRule = matchRule dotSyntax matchDotSyntax matchDotRule

execDot :: DotTree -> ExceptT BonsaiError UUnionM (UUnionM DotResult)
execDot tree = do
  symFailIfNot BonsaiTypeError (matchDotSyntax tree "term")
  mrgFmap (const ()) $ typer tree
  eval tree
