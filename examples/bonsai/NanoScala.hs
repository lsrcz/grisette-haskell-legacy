{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module NanoScala where

import BonsaiTree
import Control.Monad.Except
import Data.BitVector.Sized.Unsigned
import qualified Data.ByteString as B
import Data.Maybe
import Data.MemoTrie
import Env
import Error
import Grisette.Core
import Grisette.SymPrim.Term
import Match
import MatchSyntax
import Pattern
import SyntaxSpec

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

{-
data DotValue
  = DotEmptyValue
  | DotDummy SymBool
  | DotNamedValue (SymUnsignedBV DotBitWidth) (UnionM DotValue)
  | DotJoinValue (UnionM DotValue) (UnionM DotValue)
  deriving (Show, Eq, Generic, Mergeable SymBool, NFData)
  -}

{-
data DotResult
  = DotAny
  | DotNothing
  | DotJoinType (UnionM DotResult) (UnionM DotResult)
  | -- isType
    DotNamed Bool (SymUnsignedBV DotBitWidth) (UnionM DotResult)
  | DotRange (UnionM DotResult) (UnionM DotResult)
  deriving (Show, Eq, Generic, Mergeable SymBool, NFData, SEq SymBool)
  -}

{-
instance HasTrie DotValue where
  newtype DotValue :->: x = DotValueTrie {unDotValueTrie :: Reg DotValue :->: x}
  trie = trieGeneric DotValueTrie
  untrie = untrieGeneric unDotValueTrie
  enumerate = enumerateGeneric unDotValueTrie
  -}

{-
instance HasTrie DotResult where
  newtype DotResult :->: x = DotResultTrie {unDotResultTrie :: Reg DotResult :->: x}
  trie = trieGeneric DotResultTrie
  untrie = untrieGeneric unDotResultTrie
  enumerate = enumerateGeneric unDotResultTrie
  -}

-- $(makeUnionMWrapper "u" ''DotValue)

-- $(makeUnionMWrapper "u" ''DotResult)


{-
type DotV = UnionM (Either (SymUnsignedBV DotBitWidth) B.ByteString)

type DotValue = BonsaiTree DotV
-}

eval' :: DotTree -> Env DotBitWidth DotResult -> ExceptT BonsaiError UnionM (UnionM DotResult)
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
        mrgReturn $ dotMakeU "value" n e,
      dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \_ _ -> mrgReturn $ uBonsaiLeaf $ uRight "empty",
      dotLiteral "and" *= (placeHolder *= placeHolder) ==> \a b -> do
        av <- eval' #~ a # env
        bv <- eval' #~ b # env
        mrgReturn $ dotJoinU av bv,
      dotLiteral "var" *= placeHolder ==> \name -> do
        n <- extractName BonsaiExecError name
        mrgSingle <$> envResolve BonsaiExecError env n,
      dotLiteral "die" *= placeHolder ==> \_ -> throwError BonsaiExecError,
      dotLiteral "make-null" *= placeHolder ==> \_ -> mrgReturn $ uBonsaiLeaf $ uRight "dummy1",
      dotLiteral "null" ==> (mrgReturn $ uBonsaiLeaf $ uRight "dummy2")
    ]
    tree

eval :: DotTree -> ExceptT BonsaiError UnionM (UnionM DotResult)
eval tree = eval' tree (mrgSingle [])

type DotT = UnionM (Either (SymUnsignedBV DotBitWidth) B.ByteString)

type DotResult = BonsaiTree DotT

dotFindU ::
  B.ByteString ->
  SymUnsignedBV DotBitWidth ->
  UnionM DotResult ->
  UnionM (Maybe (UnionM DotResult))
dotFindU kind name tb = dotFind kind name #~ tb

unsafeBV :: B.ByteString -> SymUnsignedBV DotBitWidth
unsafeBV s = fromJust $ toSym $ terminalToBV dotSyntax s

andBV :: SymUnsignedBV DotBitWidth
andBV = unsafeBV "and"

terminalLiteral :: B.ByteString -> Pattern DotT 0
terminalLiteral s = literal $ uLeft $ unsafeBV s

dotFind ::
  B.ByteString ->
  SymUnsignedBV DotBitWidth ->
  DotResult ->
  UnionM (Maybe (UnionM DotResult))
dotFind kind name tb =
  mrgFmap
    ( \case
        Left _ -> Nothing
        Right v -> v
    )
    $ runExceptT
      ( bonsaiMatchCustomError
          BonsaiTypeError
          [ terminalLiteral "and" *= (placeHolder *= placeHolder) ==> \l r -> do
              lv <- lift $ dotFindU kind name l
              case lv of
                Nothing -> do
                  rv <- lift $ dotFindU kind name r
                  mrgReturn rv
                Just v -> uJust v,
            placeHolder *= placeHolder ==> \k v ->
              let e =
                    uBonsaiNode (uBonsaiLeaf $ uRight kind) (uBonsaiLeaf $ uLeft name)
               in mrgGuard (e ==~ k) (uJust v) uNothing
          ]
          tb
      )

dotMake :: B.ByteString -> SymUnsignedBV DotBitWidth -> DotResult -> DotResult
dotMake kind name tr = BonsaiNode (uBonsaiNode (uBonsaiLeaf $ uRight kind) (uBonsaiLeaf $ uLeft name)) (mrgSingle tr)

dotMakeU :: B.ByteString -> SymUnsignedBV DotBitWidth -> UnionM DotResult -> UnionM DotResult
dotMakeU kind name = uBonsaiNode (uBonsaiNode (uBonsaiLeaf $ uRight kind) (uBonsaiLeaf $ uLeft name))

dotJoin :: DotResult -> DotResult -> DotResult
dotJoin l r = BonsaiNode (uBonsaiLeaf $ uLeft andBV) (uBonsaiNode (mrgSingle l) (mrgSingle r))

dotJoinU :: UnionM DotResult -> UnionM DotResult -> UnionM DotResult
dotJoinU l r = uBonsaiNode (uBonsaiLeaf $ uLeft andBV) (uBonsaiNode l r)

uDotAny :: UnionM DotResult
uDotAny = uBonsaiLeaf $ uLeft $ unsafeBV "Any"

uDotNothing :: UnionM DotResult
uDotNothing = uBonsaiLeaf $ uLeft $ unsafeBV "Nothing"

uDotRange :: UnionM DotResult -> UnionM DotResult -> UnionM DotResult
uDotRange ufrom uto = uBonsaiNode (uBonsaiLeaf $ uLeft $ unsafeBV "range") (uBonsaiNode ufrom uto)

reduceType ::
  Int ->
  Env DotBitWidth DotResult ->
  Bool ->
  DotTree ->
  ExceptT BonsaiError UnionM (UnionM DotResult)
reduceType = {-mup memo3 $ -} \reccount env strict tree ->
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
              dotLiteral "get" *= (placeHolder *= placeHolder) ==> \tbl name -> do
                n <- extractName BonsaiTypeError name
                t <- type' #~ tbl # env
                r <- lift $ dotFindU "type" n t
                case r of
                  Nothing -> throwError BonsaiTypeError
                  Just umb -> mrgReturn umb,
              dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \name t -> do
                n <- extractName BonsaiTypeError name
                t1 <- reduceTypeR env True #~ t
                return $ dotMakeU "type" n t1,
              dotLiteral "val" *= (placeHolder *= placeHolder) ==> \name t -> do
                n <- extractName BonsaiTypeError name
                t1 <- reduceTypeR env True #~ t
                return $ dotMakeU "value" n t1,
              dotLiteral "range" *= (placeHolder *= placeHolder) ==> \f t -> do
                tfrom <- reduceTypeR env True #~ f
                tto <- reduceTypeR env True #~ t
                return $ uDotRange tfrom tto
            ]
            tree

subType :: Int -> UnionM DotResult -> UnionM DotResult -> ExceptT BonsaiError UnionM SymBool
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

type' :: DotTree -> Env DotBitWidth DotResult -> ExceptT BonsaiError UnionM (UnionM DotResult)
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
        return $ dotMakeU "value" n t,
      dotLiteral "typ" *= (placeHolder *= placeHolder) ==> \name term -> do
        n <- extractName BonsaiTypeError name
        t <- type' #~ term # env
        return $ dotMakeU "type" n t,
      dotLiteral "and" *= (placeHolder *= placeHolder) ==> \_ _ -> throwError BonsaiTypeError,
      dotLiteral "var" *= placeHolder ==> \name -> do
        n <- extractName BonsaiTypeError name
        t <- envResolve' 3 BonsaiTypeError env n
        return $ mrgSingle t,
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

typer :: DotTree -> ExceptT BonsaiError UnionM (UnionM DotResult)
typer tree = type' tree (mrgSingle [])

matchDotSyntax :: DotTree -> B.ByteString -> SymBool
matchDotSyntax = matchSyntax dotSyntax matchDotRule

matchDotRule :: Rule -> DotTree -> SymBool
matchDotRule = matchRule dotSyntax matchDotSyntax matchDotRule

execDot :: DotTree -> ExceptT BonsaiError UnionM (UnionM DotResult)
execDot tree = do
  gassertWithError BonsaiTypeError (matchDotSyntax tree "term")
  mrgFmap (const ()) $ typer tree
  eval tree
