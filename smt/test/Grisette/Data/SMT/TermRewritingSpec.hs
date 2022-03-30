{-# LANGUAGE AllowAmbiguousTypes #-}

module Grisette.Data.SMT.TermRewritingSpec where

import Control.Monad
import Data.Foldable
import qualified Data.SBV as SBV
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Num
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.SymPrim
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Grisette.Data.Prim.Integer

class (SupportedPrim b) => TermRewritingSpec a b | a -> b where
  norewriteVer :: a -> Term b
  rewriteVer :: a -> Term b
  wrap :: Term b -> Term b -> a
  same :: a -> Term Bool
  counterExample :: a -> Term Bool
  counterExample = constructUnary Not . same
  symbSpec :: String -> a
  symbSpec s = wrap (ssymbTerm s) (ssymbTerm s)
  concSpec :: b -> a
  concSpec v = wrap (concTerm v) (concTerm v)

constructUnarySpec ::
  ( TermRewritingSpec a av,
    TermRewritingSpec b bv,
    UnaryOp tag av bv
  ) =>
  tag ->
  a ->
  b
constructUnarySpec tag a =
  wrap (constructUnary tag $ norewriteVer a) (partialEvalUnary tag $ rewriteVer a)

constructBinarySpec ::
  ( TermRewritingSpec a av,
    TermRewritingSpec b bv,
    TermRewritingSpec c cv,
    BinaryOp tag av bv cv
  ) =>
  tag ->
  a ->
  b ->
  c
constructBinarySpec tag a b =
  wrap
    (constructBinary tag (norewriteVer a) (norewriteVer b))
    (partialEvalBinary tag (rewriteVer a) (rewriteVer b))

constructTernarySpec ::
  ( TermRewritingSpec a av,
    TermRewritingSpec b bv,
    TermRewritingSpec c cv,
    TermRewritingSpec d dv,
    TernaryOp tag av bv cv dv
  ) =>
  tag ->
  a ->
  b ->
  c ->
  d
constructTernarySpec tag a b c =
  wrap
    (constructTernary tag (norewriteVer a) (norewriteVer b) (norewriteVer c))
    (partialEvalTernary tag (rewriteVer a) (rewriteVer b) (rewriteVer c))

validateSpec :: (TermRewritingSpec a av, Show a, SupportedPrim av) => GrisetteSMTConfig n -> a -> Expectation
validateSpec config a = do
  r <- solveWith config (Sym $ counterExample a)
  rs <- solveWith config (Sym $ same a)
  case (r, rs) of
    (Left _, Right _) -> do
      print a
      return ()
    _ -> expectationFailure $ "Bad rewriting: " ++ pformat (norewriteVer a) ++ " was rewritten to " ++ pformat (rewriteVer a)

data BoolOnlySpec = BoolOnlySpec (Term Bool) (Term Bool)

instance Show BoolOnlySpec where
  show (BoolOnlySpec n r) = "BoolOnlySpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance TermRewritingSpec BoolOnlySpec Bool where
  norewriteVer (BoolOnlySpec n _) = n
  rewriteVer (BoolOnlySpec _ r) = r
  wrap = BoolOnlySpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

boolonly :: Int -> Gen BoolOnlySpec
boolonly 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bool")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = oneof $ return . concSpec <$> [True, False]
   in oneof [r, s]
boolonly n | n > 0 = do
  v1 <- boolonly (n - 1)
  v2 <- boolonly (n - 1)
  v3 <- boolonly (n - 1)
  oneof
    [ return $ constructUnarySpec Not v1,
      return $ constructBinarySpec And v1 v2,
      return $ constructBinarySpec Or v1 v2,
      return $ constructBinarySpec Eqv v1 v2,
      return $ constructTernarySpec ITE v1 v2 v3
    ]
boolonly _ = error "Should never be called"

instance Arbitrary BoolOnlySpec where
  arbitrary = sized boolonly

data BoolWithLIASpec = BoolWithLIASpec (Term Bool) (Term Bool)

instance Show BoolWithLIASpec where
  show (BoolWithLIASpec n r) = "BoolWithLIASpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance TermRewritingSpec BoolWithLIASpec Bool where
  norewriteVer (BoolWithLIASpec n _) = n
  rewriteVer (BoolWithLIASpec _ r) = r
  wrap = BoolWithLIASpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

data LIAWithBoolSpec = LIAWithBoolSpec (Term Integer) (Term Integer)

instance Show LIAWithBoolSpec where
  show (LIAWithBoolSpec n r) =
    "LIAWithBoolSpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance TermRewritingSpec LIAWithBoolSpec Integer where
  norewriteVer (LIAWithBoolSpec n _) = n
  rewriteVer (LIAWithBoolSpec _ r) = r
  wrap = LIAWithBoolSpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

boolWithLIA :: Int -> Gen BoolWithLIASpec
boolWithLIA 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bool")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = oneof $ return . concSpec <$> [True, False]
   in oneof [r, s]
boolWithLIA n | n > 0 = do
  v1 <- boolWithLIA (n - 1)
  v2 <- boolWithLIA (n - 1)
  v3 <- boolWithLIA (n - 1)
  v1i <- liaWithBool (n - 1)
  v2i <- liaWithBool (n - 1)
  frequency
    [ (1, return $ constructUnarySpec Not v1),
      (1, return $ constructBinarySpec And v1 v2),
      (1, return $ constructBinarySpec Or v1 v2),
      (1, return $ constructBinarySpec Eqv v1 v2),
      (5, return $ constructBinarySpec Eqv v1i v2i),
      (5, return $ constructBinarySpec LTNum v1i v2i),
      (5, return $ constructBinarySpec LENum v1i v2i),
      (1, return $ constructTernarySpec ITE v1 v2 v3)
    ]
boolWithLIA _ = error "Should never be called"

liaWithBool :: Int -> Gen LIAWithBoolSpec
liaWithBool 0 =
  let s =
        oneof $
          return . symbSpec . (++ "int")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = concSpec <$> arbitrary
   in oneof [r, s]
liaWithBool n | n > 0 = do
  v1b <- boolWithLIA (n - 1)
  v1i <- liaWithBool (n - 1)
  v2i <- liaWithBool (n - 1)
  oneof
    [ return $ constructUnarySpec UMinusNum v1i,
      return $ constructUnarySpec AbsNum v1i,
      return $ constructUnarySpec SignumNum v1i,
      return $ constructBinarySpec (AddNum @Integer) v1i v2i,
      return $ constructTernarySpec ITE v1b v1i v2i
    ]
liaWithBool _ = error "Should never be called"

instance Arbitrary BoolWithLIASpec where
  arbitrary = sized boolWithLIA

instance Arbitrary LIAWithBoolSpec where
  arbitrary = sized liaWithBool

data GeneralSpec s = GeneralSpec (Term s) (Term s)

instance (SupportedPrim s) => Show (GeneralSpec s) where
  show (GeneralSpec n r) = "GeneralSpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance (SupportedPrim s) => TermRewritingSpec (GeneralSpec s) s where
  norewriteVer (GeneralSpec n _) = n
  rewriteVer (GeneralSpec _ r) = r
  wrap = GeneralSpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

unint ::
  forall tag.
  (UnaryOp tag Integer Integer) =>
  tag ->
  GeneralSpec Integer ->
  GeneralSpec Integer
unint = constructUnarySpec

binint ::
  forall tag.
  (BinaryOp tag Integer Integer Integer) =>
  tag ->
  GeneralSpec Integer ->
  GeneralSpec Integer ->
  GeneralSpec Integer
binint = constructBinarySpec

spec :: Spec
spec = do
  let unboundedConfig = UnboundedReasoning SBV.z3
  describe "Bool only" $ do
    modifyMaxSize (const 10) $
      prop "Bool only random test" $ \(x :: BoolOnlySpec) -> do
        validateSpec unboundedConfig x
  describe "LIA" $ do
    modifyMaxSize (const 10) $
      prop "LIA randome test" $ \(x :: LIAWithBoolSpec) -> do
        validateSpec unboundedConfig x
  let times = binint TimesNum
  let add = binint (AddNum @Integer)
  let uminus = unint UMinusNum
  let divint = binint DivI
  let modint = binint ModI
  describe "Times" $ do
    it "Times on both concrete" $ do
      traverse_
        (\(x, y) -> validateSpec unboundedConfig $ times (concSpec x) (concSpec y))
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "Times on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ times (concSpec x) (symbSpec "a")
            validateSpec unboundedConfig $ times (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
    it "Two times with two concrete combined" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec unboundedConfig $ times (concSpec x) $ times (concSpec y) (symbSpec "a")
            validateSpec unboundedConfig $ times (concSpec x) $ times (symbSpec "a") (concSpec y)
            validateSpec unboundedConfig $ times (times (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec unboundedConfig $ times (times (symbSpec "a") (concSpec x)) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "Two times with one concrete" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ times (concSpec x) $ times (symbSpec "b") (symbSpec "a")
            validateSpec unboundedConfig $ times (symbSpec "b") $ times (symbSpec "a") (concSpec x)
            validateSpec unboundedConfig $ times (symbSpec "b") $ times (concSpec x) (symbSpec "a")
            validateSpec unboundedConfig $ times (times (concSpec x) (symbSpec "a")) (symbSpec "b")
            validateSpec unboundedConfig $ times (times (symbSpec "a") (concSpec x)) (symbSpec "b")
            validateSpec unboundedConfig $ times (times (symbSpec "a") (symbSpec "b")) (concSpec x)
        )
        [-3 .. 3]
    it "times and add with two concretes combined" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec unboundedConfig $ times (concSpec x) $ add (concSpec y) (symbSpec "a")
            validateSpec unboundedConfig $ times (concSpec x) $ add (symbSpec "a") (concSpec y)
            validateSpec unboundedConfig $ times (add (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec unboundedConfig $ times (add (symbSpec "a") (concSpec x)) (concSpec y)
            validateSpec unboundedConfig $ add (concSpec x) $ times (concSpec y) (symbSpec "a")
            validateSpec unboundedConfig $ add (concSpec x) $ times (symbSpec "a") (concSpec y)
            validateSpec unboundedConfig $ add (times (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec unboundedConfig $ add (times (symbSpec "a") (concSpec x)) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "times concrete with uminus symbolic" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ times (concSpec x) (uminus $ symbSpec "a")
            validateSpec unboundedConfig $ times (uminus $ symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
  describe "DivI" $ do
    it "DivI on concrete" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec unboundedConfig $ divint (concSpec x) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "DivI on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ divint (concSpec x) (symbSpec "a")
            validateSpec unboundedConfig $ divint (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
  describe "ModI" $ do
    it "ModI on concrete" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec unboundedConfig $ modint (concSpec x) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "ModI on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ modint (concSpec x) (symbSpec "a")
            validateSpec unboundedConfig $ modint (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]

