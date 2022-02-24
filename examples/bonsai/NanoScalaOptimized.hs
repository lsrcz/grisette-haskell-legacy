{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module NanoScalaOptimized where

import BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import qualified Data.ByteString as B
import Data.MemoTrie
import Env
import Error
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Match
import MatchSyntax
import Pattern
import SyntaxSpec
import Data.BitVector.Sized.Unsigned
import Data.Maybe

type DotBitWidth = 15

type DotTree = BonsaiTree (SymUnsignedBV DotBitWidth)

type ConcDotTree = ConcBonsaiTree (UnsignedBV DotBitWidth)

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

dotLiteral :: B.ByteString -> Pattern (SymUnsignedBV DotBitWidth) 0
dotLiteral s = literal $ fromJust $ toSym $ terminalToBV dotSyntax s 

data DotValue
  = DotEmptyValue
  | DotDummy SymBool
  | DotNamedValue (SymUnsignedBV DotBitWidth) (UnionM DotValue)
  | DotJoinValue (UnionM DotValue) (UnionM DotValue)
  deriving (Show, Eq, Generic, Mergeable SymBool, NFData)

data DotType
  = DotAny
  | DotNothing
  | DotJoinType (UnionM DotType) (UnionM DotType)
  | -- isType
    DotNamed Bool (SymUnsignedBV DotBitWidth) (UnionM DotType)
  | DotRange (UnionM DotType) (UnionM DotType)
  deriving (Show, Eq, Generic, Mergeable SymBool, NFData, SEq SymBool)

instance HasTrie DotValue where
  newtype DotValue :->: x = DotValueTrie {unDotValueTrie :: Reg DotValue :->: x}
  trie = trieGeneric DotValueTrie
  untrie = untrieGeneric unDotValueTrie
  enumerate = enumerateGeneric unDotValueTrie

instance HasTrie DotType where
  newtype DotType :->: x = DotTypeTrie {unDotTypeTrie :: Reg DotType :->: x}
  trie = trieGeneric DotTypeTrie
  untrie = untrieGeneric unDotTypeTrie
  enumerate = enumerateGeneric unDotTypeTrie

$(makeUnionMWrapper "u" ''DotValue)
$(makeUnionMWrapper "u" ''DotType)

eval' :: DotTree -> Env DotBitWidth DotValue -> ExceptT BonsaiError UnionM (UnionM DotValue)
eval' = {-memo2 $-} \tree env ->
  bonsaiMatchCustomError
    BonsaiExecError
    [ dotLiteral "let" *= ((placeHolder *= (placeHolder *= placeHolder)) *= (placeHolder *= placeHolder))
        ==> \name _ _ value expr -> do
          v <- eval' #~ value # env
          env1 <- envAddTree BonsaiExecError env name v
          eval' #~ expr # env1,
      dotLiteral "val" *= (placeHolder *= placeHolder) ==> \name term -> do
        n <- extractName BonsaiExecError name
        e <- eval' #~ term # env
        mrgReturn $ uDotNamedValue n e,
      dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \_ _ -> mrgReturn uDotEmptyValue,
      dotLiteral "and" *= (placeHolder *= placeHolder) ==> \a b -> do
        av <- eval' #~ a # env
        bv <- eval' #~ b # env
        mrgReturn $ uDotJoinValue av bv,
      dotLiteral "var" *= placeHolder ==> \name -> do
        n <- extractName BonsaiExecError name
        envResolveU BonsaiExecError env n,
      dotLiteral "die" *= placeHolder ==> \_ -> throwError BonsaiExecError,
      dotLiteral "make-null" *= placeHolder ==> \_ -> mrgReturn $ uDotDummy $ conc True,
      dotLiteral "null" ==> mrgReturn (uDotDummy $ conc True)
    ]
    tree

eval :: DotTree -> ExceptT BonsaiError UnionM (UnionM DotValue)
eval tree = eval' tree (mrgReturn [])

dotFindU :: Bool -> SymUnsignedBV DotBitWidth -> UnionM DotType -> UnionM (Maybe (UnionM DotType))
dotFindU isType name d = getSingle $ dotFind isType name <$> d

dotFind :: Bool -> SymUnsignedBV DotBitWidth -> DotType -> UnionM (Maybe (UnionM DotType))
dotFind isType name (DotJoinType u1 u2) = do
  u1v <- dotFindU isType name u1
  case u1v of
    Just x -> uJust x
    Nothing -> dotFindU isType name u2
dotFind isType name (DotNamed isType' n v) =
  mrgIf
    (conc (isType == isType') &&~ name ==~ n)
    (uJust v)
    uNothing
dotFind _ _ _ = uNothing

reduceType ::
  Int ->
  Env DotBitWidth DotType ->
  Bool ->
  DotTree ->
  ExceptT BonsaiError UnionM (UnionM DotType)
reduceType = {-mup memo3 $ -}\reccount env strict tree ->
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
                    mrgReturn $ uDotJoinType av bv,
              dotLiteral "get" *= (placeHolder *= placeHolder) ==> \tbl name -> do
                n <- extractName BonsaiTypeError name
                t <- type' #~ tbl # env
                r <- lift $ dotFindU True n t
                case r of
                  Nothing -> throwError BonsaiTypeError
                  Just umb -> mrgReturn umb,
              dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \name t -> do
                n <- extractName BonsaiTypeError name
                t1 <- reduceTypeR env True #~ t
                return $ uDotNamed True n t1,
              dotLiteral "val" *= (placeHolder *= placeHolder) ==> \name t -> do
                n <- extractName BonsaiTypeError name
                t1 <- reduceTypeR env True #~ t
                return $ uDotNamed False n t1,
              dotLiteral "range" *= (placeHolder *= placeHolder) ==> \f t -> do
                tfrom <- reduceTypeR env True #~ f
                tto <- reduceTypeR env True #~ t
                return $ uDotRange tfrom tto
            ]
            tree

subType :: Int -> UnionM DotType -> UnionM DotType -> ExceptT BonsaiError UnionM SymBool
subType = {-memo3 $ -}\reccount sub sup ->
  let subTypeR = subType (reccount + 1)
   in if reccount >= 3
        then throwError BonsaiTypeError
        else do
          sb <- lift sub
          case sb of
            DotNothing -> return $ conc True
            DotJoinType l r -> do
              lv <- subTypeR l sup
              rv <- subTypeR r sup
              return $ lv ||~ rv
            DotRange _ upper -> subTypeR upper sup
            _ -> do
              sp <- lift sup
              case sp of
                DotAny -> return $ conc True
                DotJoinType l r -> do
                  lv <- subTypeR sub l
                  rv <- subTypeR sub r
                  return $ lv &&~ rv
                DotRange lower _ -> subTypeR sub lower
                _ -> return $ sb ==~ sp

type' :: DotTree -> Env DotBitWidth DotType -> ExceptT BonsaiError UnionM (UnionM DotType)
type' = memo2 $ \tree env ->
  bonsaiMatchCustomError
    BonsaiTypeError
    [ dotLiteral "let" *= ((placeHolder *= (placeHolder *= placeHolder)) *= (placeHolder *= placeHolder))
        ==> \name intype outtype value expr -> do
          it <- reduceType 0 env True #~ intype
          it' <- type' #~ value # env
          subi <- subType 0 it' it
          gassertWithError BonsaiTypeError subi

          newenv <- envAddTree BonsaiTypeError env name it

          ot <- reduceType 0 newenv True #~ outtype
          ot' <- type' #~ expr # newenv
          subo <- subType 0 ot' ot
          gassertWithError BonsaiTypeError subo

          newenv' <- envAddTree BonsaiTypeError env name it'
          reduceType 0 newenv' True #~ outtype,
      dotLiteral "val" *= (placeHolder *= placeHolder) ==> \name term -> do
        n <- extractName BonsaiTypeError name
        t <- type' #~ term # env
        return $ uDotNamed False n t,
      dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \name term -> do
        n <- extractName BonsaiTypeError name
        t <- type' #~ term # env
        return $ uDotNamed True n t,
      dotLiteral "and" *= (placeHolder *= placeHolder) ==> \_ _ -> throwError BonsaiTypeError,
      dotLiteral "var" *= placeHolder ==> \name -> do
        n <- extractName BonsaiTypeError name
        t <- envResolve' 3 BonsaiTypeError env n
        return $ mrgReturn t,
      dotLiteral "die" *= placeHolder ==> \expr -> do
        t <- type' #~ expr # env
        subt <- subType 0 t uDotNothing
        gassertWithError BonsaiTypeError subt
        return t,
      dotLiteral "make-null" *= placeHolder ==> \t -> do
        t' <- reduceType 0 env False #~ t
        subt <- subType 0 t' uDotNothing
        gassertWithError BonsaiTypeError (nots subt)
        return t',
      dotLiteral "null" ==> return uDotAny
    ]
    tree

typer :: DotTree -> ExceptT BonsaiError UnionM (UnionM DotType)
typer tree = type' tree (mrgReturn [])

matchDotSyntax :: DotTree -> B.ByteString -> SymBool
matchDotSyntax = matchSyntax dotSyntax matchDotRule

matchDotRule :: Rule -> DotTree -> SymBool
matchDotRule = matchRule dotSyntax matchDotSyntax matchDotRule

execDot :: DotTree -> ExceptT BonsaiError UnionM (UnionM DotValue)
execDot tree = do
  gassertWithError BonsaiTypeError (matchDotSyntax tree "term")
  mrgFmap (const ()) $ typer tree
  eval tree
