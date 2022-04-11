{-# LANGUAGE TemplateHaskell #-}
module Grisette.Tutorial.ArithExprSynth.ArithExprSynth where

import GHC.Generics
import Grisette

data Expr
  = Const Integer
  | Add Expr Expr
  | Sub Expr Expr
  deriving (Show, Generic)
  deriving (ToCon SymExpr) via (Default Expr)

data SymExpr
  = SymConst SymInteger
  | SymAdd (UnionM SymExpr) (UnionM SymExpr)
  | SymSub (UnionM SymExpr) (UnionM SymExpr)
  deriving (Show, Generic)
  deriving (ToSym Expr, Mergeable SymBool, Evaluate Model) via (Default SymExpr)

$(makeUnionMWrapper "u" ''SymExpr)

type Op = UnionM SymExpr -> UnionM SymExpr -> UnionM SymExpr

instance GenSym SymBool () Op where

instance GenSymSimple SymBool () Op where
  genSymSimpleFresh _ = simpleChoose @SymBool [uSymAdd, uSymSub]

interpret :: SymExpr -> SymInteger
interpret (SymConst v) = v
interpret (SymAdd l r) = getSingle $ do
  vl <- l
  vr <- r
  mrgReturn $ interpret vl + interpret vr
interpret (SymSub l r) = interpret #~ l - interpret #~ r

synthExpr :: GrisetteSMTConfig n -> UnionM SymExpr -> Integer -> IO (Maybe Expr)
synthExpr config expr res = do
  r <- solveWith config $ interpret #~ expr ==~ conc res
  case r of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateToCon mo expr

sketch :: UnionM SymExpr
sketch = runGenSymFresh (do
    let v1 :: UnionM SymExpr = uSymConst 1
    let v2 :: UnionM SymExpr = uSymConst 2
    let v3 :: UnionM SymExpr = uSymConst 4
    op1 :: Op <- genSymSimpleFresh @SymBool ()
    op2 :: Op <- genSymSimpleFresh @SymBool ()
    return $ op1 v1 (op2 v2 v3)
  ) $(nameWithLoc "a")

main :: IO ()
main = do
  let config = UnboundedReasoning z3
  synthExpr config sketch (-1) >>= print
  synthExpr config sketch 7 >>= print
  synthExpr config sketch 0 >>= print