{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.Except
import GHC.Generics
import Grisette hiding (symAssert, symAssume)

a, b, c, d, e, f :: SymBool
a = "a"
b = "b"
c = "c"
d = "d"
e = "e"
f = "f"

data Error = AssertError | AssumeError
  deriving (Show, Eq, Generic)
  deriving (Mergeable SymBool) via Default Error

symAssert :: (UnionLike bool u, SymBoolOp bool, MonadError Error u) => bool -> u ()
symAssert cond = mrgIf cond (return ()) (throwError AssertError)

symAssume :: (UnionLike bool u, SymBoolOp bool, MonadError Error u) => bool -> u ()
symAssume cond = mrgIf cond (return ()) (throwError AssumeError)

-- >>> asserts
-- ExceptT (UMrg (If (! (&& a (&& (ite b c d) e))) (Single (Left AssertError)) (Single (Right ()))))
asserts :: ExceptT Error UnionM ()
asserts = do
  symAssert a
  mrgIf b (symAssert c) (symAssert d)
  symAssert e

-- >>> mixed
-- ExceptT (UMrg (If (! (&& a (&& (ite b c d) (&& e f)))) (If (&& a (ite (ite b c d) e b)) (Single (Left AssertError)) (Single (Left AssumeError))) (Single (Right ()))))
mixed :: ExceptT Error UnionM ()
mixed = do
  symAssume a
  mrgIf b (symAssert c) (symAssume d)
  symAssume e
  symAssert f

simpleTranslation :: Either Error () -> SymBool
simpleTranslation (Left AssertError) = conc True
simpleTranslation _ = conc False

main :: IO ()
main = do
  print asserts
  print mixed
  _ <- solveFallable (UnboundedReasoning z3 {verbose = True}) simpleTranslation $ runExceptT $ mixed
  return ()
