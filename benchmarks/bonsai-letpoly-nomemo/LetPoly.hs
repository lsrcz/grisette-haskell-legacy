{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module LetPoly where

import Bonsai.BonsaiTree
import Control.DeepSeq
import Control.Monad.Except
import Data.BitVector.Sized.Unsigned
import qualified Data.ByteString as B
import Data.Maybe
import Bonsai.Env
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Bonsai.Match
import Bonsai.MatchSyntaxNoMemo
import Bonsai.Pattern
import Bonsai.SyntaxSpec
import Data.Hashable

type LetPolyWidth = 19

type LetPolyTree = BonsaiTree (SymUnsignedBV LetPolyWidth)

type ConcLetPolyTree = ConcBonsaiTree (UnsignedBV LetPolyWidth)

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

letPolyLiteral :: B.ByteString -> Pattern (SymUnsignedBV LetPolyWidth) 0
letPolyLiteral s = literal $ fromJust $ toSym $ terminalToBV letPolySyntax s

simpleNode :: B.ByteString -> LetPolyTree
simpleNode = unsafeLeaf letPolySyntax

pairNode :: LetPolyTree -> LetPolyTree -> LetPolyTree
pairNode l r = BonsaiNode (mrgReturn l) (mrgReturn r)

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
refTyU = BonsaiNode (mrgReturn $ simpleNode "ref")

arrowTy :: LetPolyTree -> LetPolyTree -> LetPolyTree
arrowTy = pairNode

arrowTyU :: UnionM LetPolyTree -> UnionM LetPolyTree -> LetPolyTree
arrowTyU = BonsaiNode

tyassert :: SymBool -> ExceptT BonsaiError UnionM ()
tyassert = gassertWithError BonsaiTypeError

tyMatch ::
  (Mergeable SymBool t, Show t) =>
  [PatternHandler (SymUnsignedBV LetPolyWidth) BonsaiError t] ->
  LetPolyTree ->
  ExceptT BonsaiError UnionM t
tyMatch = bonsaiMatchCustomError BonsaiTypeError

typeCompatible :: LetPolyTree -> LetPolyTree -> ExceptT BonsaiError UnionM ()
typeCompatible current expect =
  tyMatch
    [ letPolyLiteral "int" ==> (tyassert $! current ==~ intTy),
      letPolyLiteral "bool" ==> (tyassert $! current ==~ boolTy),
      letPolyLiteral "any" ==> (return $! ()),
      letPolyLiteral "ref" *= placeHolder ==> \t1 ->
        tyMatch
          [ letPolyLiteral "ref" *= placeHolder ==> \t2 ->
              typeCompatible #~ t2 #~ t1
          ]
          current,
      placeHolder *= placeHolder ==> \i o ->
        tyMatch
          [ letPolyLiteral "ref" *= placeHolder ==> \_ -> tyassert $ conc False,
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
derefTy = tyMatch [letPolyLiteral "ref" *= placeHolder ==> return]

typer' :: LetPolyTree -> Env LetPolyWidth LetPolyTree -> ExceptT BonsaiError UnionM (UnionM LetPolyTree)
typer' tree env =
  tyMatch
    [ letPolyLiteral "true" ==> (return $! mrgReturn boolTy),
      letPolyLiteral "one" ==> (return $! mrgReturn intTy),
      letPolyLiteral "!" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        typeCompatible #~ t # boolTy
        return $! mrgReturn boolTy,
      letPolyLiteral "-" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        typeCompatible #~ t # intTy
        return $! mrgReturn intTy,
      letPolyLiteral "&" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        return $! mrgReturn $ refTyU t,
      letPolyLiteral "*" *= placeHolder ==> \v -> do
        t <- typer' #~ v # env
        derefTy #~ t,
      ((letPolyLiteral "let" *= placeHolder) *= placeHolder) *= placeHolder ==> \name v expr -> do
        n <- extractName BonsaiTypeError name
        isValidName BonsaiTypeError n
        t <- typer' #~ v # env
        let newenv = envAdd env n t
        typer' #~ expr # newenv,
      ((letPolyLiteral ":=" *= placeHolder) *= placeHolder) *= placeHolder ==> \name expr1 expr2 -> do
        rt <- typer' #~ name # env
        dt <- derefTy #~ rt
        e1ty <- typer' #~ expr1 # env

        typeCompatible #~ e1ty #~ dt
        typer' #~ expr2 # env,
      (letPolyLiteral "lambda" *= placeHolder) *= (placeHolder *= placeHolder) ==> \name ty expr -> do
        n <- extractName BonsaiTypeError name
        isValidName BonsaiTypeError n
        let newenv = envAdd env n ty
        exprTy <- typer' #~ expr # newenv
        return $! mrgReturn $ arrowTyU ty exprTy,
      letPolyLiteral "call" *= (placeHolder *= placeHolder) ==> \func arg -> do
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
typer tree = typer' tree (mrgReturn [])

data LetPolyValue
  = LetPolyInt SymInteger
  | LetPolyBool SymBool
  | LetPolyRefCell (UnionM Integer)
  | LetPolyLambda (SymUnsignedBV LetPolyWidth) (UnionM LetPolyTree) (Env LetPolyWidth LetPolyValue)
  deriving (Show, Eq, Generic, NFData, Hashable)
  deriving (Evaluate Model, SEq SymBool) via (Default LetPolyValue)

instance Mergeable SymBool LetPolyValue where
  mergeStrategy =
    OrderedStrategy
      ( \case
          LetPolyInt _ -> 0 :: Int
          LetPolyBool _ -> 1
          LetPolyRefCell _ -> 2
          LetPolyLambda _ _ _ -> 3
      )
      ( htmemo $ \case
          0 -> SimpleStrategy $ \cond (LetPolyInt l) (LetPolyInt r) -> LetPolyInt $ mrgIte cond l r
          1 -> SimpleStrategy $ \cond (LetPolyBool l) (LetPolyBool r) -> LetPolyBool $ mrgIte cond l r
          2 -> SimpleStrategy $ \cond (LetPolyRefCell l) (LetPolyRefCell r) -> LetPolyRefCell $ mrgIf cond l r
          3 -> SimpleStrategy $ \cond (LetPolyLambda n1 v1 e1) (LetPolyLambda n2 v2 e2) ->
            LetPolyLambda (mrgIte cond n1 n2) (mrgIte cond v1 v2) (mrgIte cond e1 e2)
          _ -> error "Should not happen"
      )

$(makeUnionMWrapper "u" ''LetPolyValue)

newtype RefEnv = RefEnv [(Integer, UnionM (Maybe (UnionM LetPolyValue)))]
  deriving (Show, Eq, Generic, Hashable)

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
  mergeStrategy = SimpleStrategy mrgIte

instance SimpleMergeable SymBool RefEnv where
  mrgIte cond (RefEnv t) (RefEnv f) = RefEnv $ go t f
    where
      go [] [] = []
      go [] ((fi, fv) : fs) = (fi, mrgIf cond uNothing fv) : go [] fs
      go ((ti, tv) : ts) [] = (ti, mrgIf cond tv uNothing) : go ts []
      go tl@((ti, tv) : ts) fl@((fi, fv) : fs)
        | ti > fi = (ti, mrgIte cond tv uNothing) : go ts fl
        | ti == fi = (ti, mrgIte cond tv fv) : go ts fs
        | otherwise = (fi, mrgIte cond uNothing fv) : go tl fs

type EvalType =
  Env LetPolyWidth LetPolyValue ->
  RefEnv ->
  LetPolyTree ->
  ExceptT BonsaiError UnionM (UnionM LetPolyValue, RefEnv)

simpleEvalList ::
  EvalType ->
  Env LetPolyWidth LetPolyValue ->
  RefEnv ->
  [PatternHandler (SymUnsignedBV LetPolyWidth) BonsaiError (UnionM LetPolyValue, RefEnv)]
simpleEvalList evalFunc named ref =
  [ letPolyLiteral "true" ==> uTuple2 (uLetPolyBool $ conc True) ref,
    letPolyLiteral "one" ==> uTuple2 (uLetPolyInt 1) ref,
    letPolyLiteral "!" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      v1 <- lift v
      case v1 of
        LetPolyBool sym -> uTuple2 (uLetPolyBool (nots sym)) newRef
        _ -> throwError BonsaiExecError,
    letPolyLiteral "-" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      v1 <- lift v
      case v1 of
        LetPolyInt sym -> uTuple2 (uLetPolyInt (negate sym)) newRef
        _ -> throwError BonsaiExecError,
    letPolyLiteral "&" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      let ptr = minimumAvailableNum newRef
      uTuple2 (uLetPolyRefCell $ mrgReturn ptr) (updateRefEnv ptr v newRef),
    letPolyLiteral "*" *= placeHolder ==> \t -> do
      (v, newRef) <- evalFunc named ref #~ t
      v1 <- lift v
      case v1 of
        LetPolyRefCell ptr -> do
          res <- getRefEnv #~ ptr # newRef
          uTuple2 res newRef
        _ -> throwError BonsaiExecError,
    (letPolyLiteral "lambda" *= placeHolder) *= (placeHolder *= placeHolder) ==> \name _ expr -> do
      n <- extractName BonsaiExecError name
      isValidName BonsaiExecError n
      uTuple2 (uLetPolyLambda n expr named) ref,
    ((letPolyLiteral ":=" *= placeHolder) *= placeHolder) *= placeHolder ==> \cell v1 expr -> do
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
  [PatternHandler (SymUnsignedBV LetPolyWidth) BonsaiError t] ->
  LetPolyTree ->
  ExceptT BonsaiError UnionM t
evalMatch = bonsaiMatchCustomError BonsaiExecError

simpleEval' :: EvalType
simpleEval' named ref tree =
  evalMatch
    (simpleEvalList simpleEval' named ref)
    tree

eval' :: EvalType
eval' named ref tree =
  evalMatch
    ( [ ((letPolyLiteral "let" *= placeHolder) *= placeHolder) *= placeHolder ==> \name v1 v2 -> do
          n <- extractName BonsaiExecError name
          isValidName BonsaiExecError n
          (v1r, newRef) <- eval' named ref #~ v1
          let newNamed = envAdd named n v1r
          eval' newNamed newRef #~ v2,
        letPolyLiteral "call" *= (placeHolder *= placeHolder) ==> \func arg -> do
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
  (v, _) <- eval' (mrgReturn []) (RefEnv []) tree
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
