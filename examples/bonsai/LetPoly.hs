{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module LetPoly where

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

type LetPolyWidth = 19

type LetPolyTree = BonsaiTree LetPolyWidth

type ConcLetPolyTree = ConcBonsaiTree LetPolyWidth

letPolySyntax :: OptimSyntaxSpec LetPolyWidth
letPolySyntax =
  buildSyntax
    [ "term"
        --> [ (("let" -* "name") -* "term") -* "term",
              "call" -* ("term" -* "term"),
              "easy-term"
            ],
      "easy-term"
        --> [ "true",
              "one",
              ((":=" -* "name") -* "term") -* "term",
              ("lambda" -* "name") -* ("type" -* "easy-term"),
              "op-type" -* "term",
              "name"
            ],
      "type"
        --> [ "int",
              "bool",
              "any",
              "ref" -* "type",
              "type" -* "type"
            ],
      "op-type" --> ["!", "-", "&", "*"],
      "name" --> ["a", "b", "c", "d", "e"]
    ]

simpleNode :: B.ByteString -> LetPolyTree
simpleNode = unsafeLeaf letPolySyntax

pairNode :: LetPolyTree -> LetPolyTree -> LetPolyTree
pairNode l r = BonsaiNode (mrgSingle l) (mrgSingle r)

letTerm :: B.ByteString -> LetPolyTree -> LetPolyTree -> LetPolyTree
letTerm name t1 = pairNode (pairNode (pairNode (simpleNode "let") (simpleNode name)) t1)

callTerm :: LetPolyTree -> LetPolyTree -> LetPolyTree
callTerm l r = pairNode (simpleNode "call") $ pairNode l r

trueTerm :: LetPolyTree
trueTerm = simpleNode "true"

oneTerm :: LetPolyTree
oneTerm = simpleNode "one"

assignTerm :: LetPolyTree -> LetPolyTree -> LetPolyTree -> LetPolyTree
assignTerm ref t1 = pairNode (pairNode (pairNode (simpleNode ":=") ref) t1)

lambdaTerm :: B.ByteString -> LetPolyTree -> LetPolyTree -> LetPolyTree
lambdaTerm name t1 t2 =
  pairNode (pairNode (simpleNode "lambda") (simpleNode name)) $
    pairNode t1 t2

opTerm :: B.ByteString -> LetPolyTree -> LetPolyTree
opTerm op = pairNode (simpleNode op)

nameTerm :: B.ByteString -> LetPolyTree
nameTerm = simpleNode

intTy :: LetPolyTree
intTy = simpleNode "int"

boolTy :: LetPolyTree
boolTy = simpleNode "bool"

anyTy :: LetPolyTree
anyTy = simpleNode "any"

refTy :: LetPolyTree -> LetPolyTree
refTy = pairNode (simpleNode "ref")

refTyU :: UnionM LetPolyTree -> LetPolyTree
refTyU = BonsaiNode (mrgSingle $ simpleNode "ref")

arrowTy :: LetPolyTree -> LetPolyTree -> LetPolyTree
arrowTy = pairNode

arrowTyU :: UnionM LetPolyTree -> UnionM LetPolyTree -> LetPolyTree
arrowTyU = BonsaiNode

tyassert :: SymBool -> ExceptT BonsaiError UnionM ()
tyassert = gassertWithError BonsaiTypeError

tyMatch ::
  (Mergeable SymBool t, Show t) =>
  [PatternHandler LetPolyWidth BonsaiError t] ->
  LetPolyTree ->
  ExceptT BonsaiError UnionM t
tyMatch = bonsaiMatchCustomError BonsaiTypeError letPolySyntax

typeCompatible :: LetPolyTree -> LetPolyTree -> ExceptT BonsaiError UnionM ()
typeCompatible = memo2 $ \current expect ->
  tyMatch
    [ literal "int" ==> (tyassert $! current ==~ intTy),
      literal "bool" ==> (tyassert $! current ==~ boolTy),
      literal "any" ==> (return $! ()),
      literal "ref" *= placeHolder ==> \t1 ->
        tyMatch
          [ literal "ref" *= placeHolder ==> \t2 ->
              typeCompatible #~ t2 #~ t1
          ]
          current,
      placeHolder *= placeHolder ==> \i o ->
        tyMatch
          [ literal "ref" *= placeHolder ==> \_ -> tyassert $ conc False,
            placeHolder *= placeHolder ==> \i1 o1 -> do
              typeCompatible #~ i1 #~ i
              typeCompatible #~ o1 #~ o
          ]
          current
    ]
    expect

isValidName :: BonsaiError -> SymUnsignedBV LetPolyWidth -> ExceptT BonsaiError UnionM ()
isValidName err sym =
  gassertWithError err $
    foldl
      ( \acc v ->
          acc
            ||~ Just sym ==~ (conc <$> terminalToBV letPolySyntax v)
      )
      (conc False)
      ["a", "b", "c", "d", "e"]

derefTy :: LetPolyTree -> ExceptT BonsaiError UnionM (UnionM LetPolyTree)
derefTy = tyMatch [literal "ref" *= placeHolder ==> return]

typer' :: LetPolyTree -> Env LetPolyWidth LetPolyTree -> ExceptT BonsaiError UnionM (UnionM LetPolyTree)
typer' = memo2 $ \tree env ->
  tyMatch
    [ literal "true" ==> (return $! mrgSingle boolTy),
      literal "one" ==> (return $! mrgSingle intTy),
      literal "!" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        typeCompatible #~ t # boolTy
        return $! mrgSingle boolTy,
      literal "-" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        typeCompatible #~ t # intTy
        return $! mrgSingle intTy,
      literal "&" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        return $! mrgSingle $ refTyU t,
      literal "*" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        derefTy #~ t,
      ((literal "let" *= placeHolder) *= placeHolder) *= placeHolder ==> \name v expr -> do
        n <- extractName BonsaiTypeError name
        isValidName BonsaiTypeError n
        t <- typer' #~ v # env
        let newenv = envAdd env n t
        typer' #~ expr # newenv,
      ((literal ":=" *= placeHolder) *= placeHolder) *= placeHolder ==> \name expr1 expr2 -> do
        rt <- typer' #~ name # env
        dt <- derefTy #~ rt
        e1ty <- typer' #~ expr1 # env

        typeCompatible #~ e1ty #~ dt
        typer' #~ expr2 # env,
      (literal "lambda" *= placeHolder) *= (placeHolder *= placeHolder) ==> \name ty expr -> do
        n <- extractName BonsaiTypeError name
        isValidName BonsaiTypeError n
        let newenv = envAdd env n ty
        exprTy <- typer' #~ expr # newenv
        return $! mrgSingle $ arrowTyU ty exprTy,
      literal "call" *= (placeHolder *= placeHolder) ==> \func arg -> do
        ft <- typer' #~ func # env
        ftx <- lift ft
        case ftx of
          BonsaiNode funcArgTy funcResTy -> do
            argTy <- typer' #~ arg # env
            typeCompatible #~ argTy #~ funcArgTy
            return $! funcResTy
          _ -> throwError $! BonsaiTypeError,
      placeHolder ==> \v -> do
        n <- extractName BonsaiTypeError v
        envResolveU BonsaiTypeError env n
    ]
    tree

typer :: LetPolyTree -> ExceptT BonsaiError UnionM (UnionM LetPolyTree)
typer tree = typer' tree (mrgSingle [])

data LetPolyValue
  = LetPolyInt SymInteger
  | LetPolyBool SymBool
  | LetPolyRefCell (UnionM Integer)
  | LetPolyLambda (SymUnsignedBV LetPolyWidth) (UnionM LetPolyTree) (Env LetPolyWidth LetPolyValue)
  deriving (Show, Eq, Generic, SEq SymBool, NFData, SymEval Model)

instance Mergeable SymBool LetPolyValue where
  mergeStrategy = OrderedStrategy (\case
    LetPolyInt _ -> 0 :: Int
    LetPolyBool _ -> 1
    LetPolyRefCell _ -> 2
    LetPolyLambda _ _ _ -> 3)
    (memo $ \case
      0 -> SimpleStrategy $ \cond (LetPolyInt l) (LetPolyInt r) -> LetPolyInt $ mrgIf @SymBool cond l r
      1 -> SimpleStrategy $ \cond (LetPolyBool l) (LetPolyBool r) -> LetPolyBool $ mrgIf @SymBool cond l r
      2 -> SimpleStrategy $ \cond (LetPolyRefCell l) (LetPolyRefCell r) -> LetPolyRefCell $ mrgIf @SymBool cond l r
      3 -> SimpleStrategy $ \cond (LetPolyLambda n1 v1 e1) (LetPolyLambda n2 v2 e2) ->
        LetPolyLambda (mrgIf @SymBool cond n1 n2) (mrgIf @SymBool cond v1 v2) (mrgIf @SymBool cond e1 e2))
    

instance HasTrie LetPolyValue where
  newtype LetPolyValue :->: x = LetPolyValueTrie {unLetPolyValueTrie :: Reg LetPolyValue :->: x}
  trie = trieGeneric LetPolyValueTrie
  untrie = untrieGeneric unLetPolyValueTrie
  enumerate = enumerateGeneric unLetPolyValueTrie

$(makeUnionMWrapper "u" ''LetPolyValue)

newtype RefEnv = RefEnv [(Integer, UnionM (Maybe (UnionM LetPolyValue)))]
  deriving (Show, Eq, Generic)

minimumAvailableNum :: RefEnv -> Integer
minimumAvailableNum (RefEnv []) = 0
minimumAvailableNum (RefEnv ((i, _) : _)) = i + 1

updateRefEnv :: Integer -> UnionM LetPolyValue -> RefEnv -> RefEnv
updateRefEnv i t (RefEnv l) = RefEnv $ go l
  where
    go [] = [(i, uJust t)]
    go l1@((j, t1) : ls)
      | i > j = (i, uJust t) : l1
      | i == j = (i, uJust t) : ls
      | otherwise = (j, t1) : go ls

getRefEnv :: Integer -> RefEnv -> ExceptT BonsaiError UnionM (UnionM LetPolyValue)
getRefEnv i (RefEnv l) = go l
  where
    go [] = throwError BonsaiExecError
    go ((x, t) : xs)
      | i < x = go xs
      | i == x = do
        t1 <- lift t
        case t1 of
          Nothing -> throwError BonsaiExecError
          Just v -> mrgReturn v
      | otherwise = throwError BonsaiExecError

instance Mergeable SymBool RefEnv where
  mergeStrategy = SimpleStrategy mrgIf

instance SimpleMergeable SymBool RefEnv where
  mrgIf cond (RefEnv t) (RefEnv f) = RefEnv $ go t f
    where
      go [] [] = []
      go [] ((fi, fv) : fs) = (fi, mrgGuard cond uNothing fv) : go [] fs
      go ((ti, tv) : ts) [] = (ti, mrgGuard cond tv uNothing) : go ts []
      go tl@((ti, tv) : ts) fl@((fi, fv) : fs)
        | ti > fi = (ti, mrgGuard cond tv uNothing) : go ts fl
        | ti == fi = (ti, mrgGuard cond tv fv) : go ts fs
        | otherwise = (fi, mrgGuard cond uNothing fv) : go tl fs

instance HasTrie RefEnv where
  newtype RefEnv :->: x = RefEnvTrie {unRefEnvTrie :: Reg RefEnv :->: x}
  trie = trieGeneric RefEnvTrie
  untrie = untrieGeneric unRefEnvTrie
  enumerate = enumerateGeneric unRefEnvTrie

type EvalType =
  Env LetPolyWidth LetPolyValue ->
  RefEnv ->
  LetPolyTree ->
  ExceptT BonsaiError UnionM (UnionM LetPolyValue, RefEnv)

simpleEvalList ::
  EvalType ->
  Env LetPolyWidth LetPolyValue ->
  RefEnv ->
  [PatternHandler LetPolyWidth BonsaiError (UnionM LetPolyValue, RefEnv)]
simpleEvalList evalFunc named ref =
  [ literal "true" ==> uTuple2 (uLetPolyBool $ conc True) ref,
    literal "one" ==> uTuple2 (uLetPolyInt 1) ref,
    literal "!" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      v1 <- lift v
      case v1 of
        LetPolyBool sym -> uTuple2 (uLetPolyBool (nots sym)) newRef
        _ -> throwError BonsaiExecError,
    literal "-" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      v1 <- lift v
      case v1 of
        LetPolyInt sym -> uTuple2 (uLetPolyInt (negate sym)) newRef
        _ -> throwError BonsaiExecError,
    literal "&" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      let ptr = minimumAvailableNum newRef
      uTuple2 (uLetPolyRefCell $ mrgSingle ptr) (updateRefEnv ptr v newRef),
    literal "*" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      v1 <- lift v
      case v1 of
        LetPolyRefCell ptr -> do
          res <- getRefEnv #~ ptr # newRef
          uTuple2 res newRef
        _ -> throwError BonsaiExecError,
    (literal "lambda" *= placeHolder) *= (placeHolder *= placeHolder) ==> \name _ expr -> do
      n <- extractName BonsaiExecError name
      isValidName BonsaiExecError n
      uTuple2 (uLetPolyLambda n expr named) ref,
    ((literal ":=" *= placeHolder) *= placeHolder) *= placeHolder ==> \cell v1 expr -> do
      (c, newRef) <- evalFunc named ref #~ cell
      (v, newRef2) <- evalFunc named newRef #~ v1
      c1 <- lift c
      case c1 of
        LetPolyRefCell ptr -> do
          let newRef3 = updateRefEnv #~ ptr # v # newRef2
          evalFunc named newRef3 #~ expr
        _ -> throwError BonsaiExecError,
    placeHolder ==> \v -> do
      n <- extractName BonsaiExecError v
      isValidName BonsaiExecError n
      m <- envResolveU BonsaiExecError named n
      uTuple2 m ref
  ]

evalMatch ::
  (Mergeable SymBool t, Show t) =>
  [PatternHandler LetPolyWidth BonsaiError t] ->
  LetPolyTree ->
  ExceptT BonsaiError UnionM t
evalMatch = bonsaiMatchCustomError BonsaiExecError letPolySyntax

simpleEval' :: EvalType
simpleEval' = memo3 $ \named ref tree ->
  evalMatch
    (simpleEvalList simpleEval' named ref)
    tree

eval' :: EvalType
eval' = memo3 $ \named ref tree ->
  evalMatch
    ( [ ((literal "let" *= placeHolder) *= placeHolder) *= placeHolder ==> \name v1 v2 -> do
          n <- extractName BonsaiExecError name
          isValidName BonsaiExecError n
          (v1r, newRef) <- eval' named ref #~ v1
          let newNamed = envAdd named n v1r
          eval' newNamed newRef #~ v2,
        literal "call" *= (placeHolder *= placeHolder) ==> \func arg -> do
          (funcv, newRef) <- eval' named ref #~ func
          x <- lift arg
          (argv, newRef1) <- eval' named newRef x
          funcv1 <- lift funcv
          case funcv1 of
            LetPolyLambda sym funcVal funcEnv -> do
              let newEnv = envAdd funcEnv sym argv
              simpleEval' newEnv newRef1 #~ funcVal
            _ -> throwError BonsaiExecError
      ]
        ++ simpleEvalList eval' named ref
    )
    tree

eval :: LetPolyTree -> ExceptT BonsaiError UnionM (UnionM LetPolyValue)
eval tree = do
  (v, _) <- eval' (mrgSingle []) (RefEnv []) tree
  mrgReturn v

matchLetPolySyntax :: LetPolyTree -> B.ByteString -> SymBool
matchLetPolySyntax = matchSyntax letPolySyntax matchLetPolyRule

matchLetPolyRule :: Rule -> LetPolyTree -> SymBool
matchLetPolyRule = matchRule letPolySyntax matchLetPolySyntax matchLetPolyRule

execLetPoly :: LetPolyTree -> ExceptT BonsaiError UnionM (UnionM LetPolyValue)
execLetPoly tree = do
  gassertWithError BonsaiTypeError (matchLetPolySyntax tree "term")
  mrgFmap (const ()) $ typer tree
  -- return $ uLetPolyInt 1
  eval tree
