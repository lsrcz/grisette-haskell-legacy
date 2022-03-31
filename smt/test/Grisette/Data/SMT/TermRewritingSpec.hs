{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Data.SMT.TermRewritingSpec where

import qualified Data.BitVector.Sized.Signed as BVS
import Data.Bits
import Data.Foldable
import Data.Proxy
import qualified Data.SBV as SBV
import GHC.TypeLits
import Grisette.Data.Prim.BV (BVTConcat (..), BVTExt (..), BVTExtract (..), UnderlyingBV)
import Grisette.Data.Prim.Bits
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Num
import Grisette.Data.SMT.Config
import Grisette.Data.SMT.Solving
import Grisette.Data.SymPrim
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

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
    (Left _, Left _) -> do
      expectationFailure $ "Bad rewriting with unsolvable formula: " ++ pformat (norewriteVer a) ++ " was rewritten to " ++ pformat (rewriteVer a)
    (Right m, _) -> do
      print a
      print $ counterExample $ a
      print $ same $ a
      expectationFailure $ "With model" ++ show m ++ "Bad rewriting: " ++ pformat (norewriteVer a) ++ " was rewritten to " ++ pformat (rewriteVer a)

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

data FixedSizedBVWithBoolSpec bv = FixedSizedBVWithBoolSpec (Term (bv 4)) (Term (bv 4))

instance (SupportedPrim (bv 4)) => Show (FixedSizedBVWithBoolSpec bv) where
  show (FixedSizedBVWithBoolSpec n r) = "FixedSizedBVWithBoolSpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance (SupportedPrim (bv 4)) => TermRewritingSpec (FixedSizedBVWithBoolSpec bv) (bv 4) where
  norewriteVer (FixedSizedBVWithBoolSpec n _) = n
  rewriteVer (FixedSizedBVWithBoolSpec _ r) = r
  wrap = FixedSizedBVWithBoolSpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

data BoolWithFixedSizedBVSpec (bv :: Nat -> *) = BoolWithFixedSizedBVSpec (Term Bool) (Term Bool)

instance Show (BoolWithFixedSizedBVSpec bv) where
  show (BoolWithFixedSizedBVSpec n r) =
    "BoolWithFixedSizedBVSpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance TermRewritingSpec (BoolWithFixedSizedBVSpec bv) Bool where
  norewriteVer (BoolWithFixedSizedBVSpec n _) = n
  rewriteVer (BoolWithFixedSizedBVSpec _ r) = r
  wrap = BoolWithFixedSizedBVSpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

boolWithFSBV :: forall proxy bv. (SupportedPrim (bv 4), Ord (bv 4), Num (bv 4), Bits (bv 4)) => proxy bv -> Int -> Gen (BoolWithFixedSizedBVSpec bv)
boolWithFSBV _ 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bool")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = oneof $ return . concSpec <$> [True, False]
   in oneof [r, s]
boolWithFSBV p n | n > 0 = do
  v1 <- boolWithFSBV p (n - 1)
  v2 <- boolWithFSBV p (n - 1)
  v3 <- boolWithFSBV p (n - 1)
  v1i <- fsbvWithBool p (n - 1)
  v2i <- fsbvWithBool p (n - 1)
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
boolWithFSBV _ _ = error "Should never be called"

fsbvWithBool ::
  forall proxy bv.
  (SupportedPrim (bv 4), Ord (bv 4), Num (bv 4), Bits (bv 4)) =>
  proxy bv ->
  Int ->
  Gen (FixedSizedBVWithBoolSpec bv)
fsbvWithBool _ 0 =
  let s =
        oneof $
          return . symbSpec . (++ "int")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = concSpec . fromInteger <$> arbitrary
   in oneof [r, s]
fsbvWithBool p n | n > 0 = do
  v1b <- boolWithFSBV p (n - 1)
  v1i <- fsbvWithBool p (n - 1)
  v2i <- fsbvWithBool p (n - 1)
  i <- arbitrary
  oneof
    [ return $ constructUnarySpec UMinusNum v1i,
      return $ constructUnarySpec AbsNum v1i,
      return $ constructUnarySpec SignumNum v1i,
      return $ constructBinarySpec (AddNum @(bv 4)) v1i v2i,
      return $ constructBinarySpec TimesNum v1i v2i,
      return $ constructBinarySpec (AndBits @(bv 4)) v1i v2i,
      return $ constructBinarySpec (OrBits @(bv 4)) v1i v2i,
      return $ constructBinarySpec (XorBits @(bv 4)) v1i v2i,
      return $ constructUnarySpec (ComplementBits @(bv 4)) v1i,
      return $ constructUnarySpec (ShiftBits @(bv 4) i) v1i,
      return $ constructUnarySpec (RotateBits @(bv 4) i) v1i,
      return $ constructTernarySpec ITE v1b v1i v2i
    ]
fsbvWithBool _ _ = error "Should never be called"

instance (SupportedPrim (bv 4), Ord (bv 4), Num (bv 4), Bits (bv 4)) => Arbitrary (BoolWithFixedSizedBVSpec bv) where
  arbitrary = sized (boolWithFSBV (Proxy @bv))

instance (SupportedPrim (bv 4), Ord (bv 4), Num (bv 4), Bits (bv 4)) => Arbitrary (FixedSizedBVWithBoolSpec bv) where
  arbitrary = sized (fsbvWithBool Proxy)

data DifferentSizeBVSpec bv (n :: Nat) = DifferentSizeBVSpec (Term (bv n)) (Term (bv n))

instance (SupportedPrim (bv n)) => Show (DifferentSizeBVSpec bv n) where
  show (DifferentSizeBVSpec n r) = "DSizeBVSpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance (SupportedPrim (bv n)) => TermRewritingSpec (DifferentSizeBVSpec bv n) (bv n) where
  norewriteVer (DifferentSizeBVSpec n _) = n
  rewriteVer (DifferentSizeBVSpec _ r) = r
  wrap = DifferentSizeBVSpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

type SupportedBV bv (n :: Nat) =
  (SupportedPrim (bv n), Ord (bv n), Num (bv n), Bits (bv n))

dsbv1 ::
  forall proxy bv.
  ( SupportedBV bv 1,
    SupportedBV bv 2,
    SupportedBV bv 3,
    SupportedBV bv 4,
    UnderlyingBV bv
  ) =>
  proxy bv ->
  Int ->
  Gen (DifferentSizeBVSpec bv 1)
dsbv1 _ 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bv1")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = concSpec . fromInteger <$> arbitrary
   in oneof [r, s]
dsbv1 p depth | depth > 0 = do
  v1 <- dsbv1 p (depth - 1)
  v1' <- dsbv1 p (depth - 1)
  v2 <- dsbv2 p (depth - 1)
  v3 <- dsbv3 p (depth - 1)
  v4 <- dsbv4 p (depth - 1)
  i <- arbitrary
  oneof
    [ return $ constructUnarySpec UMinusNum v1,
      return $ constructUnarySpec AbsNum v1,
      return $ constructUnarySpec SignumNum v1,
      return $ constructBinarySpec (AddNum @(bv 1)) v1 v1',
      return $ constructBinarySpec TimesNum v1 v1',
      return $ constructBinarySpec (AndBits @(bv 1)) v1 v1',
      return $ constructBinarySpec (OrBits @(bv 1)) v1 v1',
      return $ constructBinarySpec (XorBits @(bv 1)) v1 v1',
      return $ constructUnarySpec (ComplementBits @(bv 1)) v1,
      return $ constructUnarySpec (ShiftBits @(bv 1) i) v1,
      return $ constructUnarySpec (RotateBits @(bv 1) i) v1,
      return $ constructUnarySpec (BVTExtract @0 @1 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @1 @1 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @2 @1 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @3 @1 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @0 @1 @3 Proxy) v3,
      return $ constructUnarySpec (BVTExtract @1 @1 @3 Proxy) v3,
      return $ constructUnarySpec (BVTExtract @2 @1 @3 Proxy) v3,
      return $ constructUnarySpec (BVTExtract @0 @1 @2 Proxy) v2,
      return $ constructUnarySpec (BVTExtract @1 @1 @2 Proxy) v2,
      return $ constructUnarySpec (BVTExtract @0 @1 @1 Proxy) v1
    ]
dsbv1 _ _ = error "Should never be called"

dsbv2 ::
  forall proxy bv.
  ( SupportedBV bv 1,
    SupportedBV bv 2,
    SupportedBV bv 3,
    SupportedBV bv 4,
    UnderlyingBV bv
  ) =>
  proxy bv ->
  Int ->
  Gen (DifferentSizeBVSpec bv 2)
dsbv2 _ 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bv2")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = concSpec . fromInteger <$> arbitrary
   in oneof [r, s]
dsbv2 p depth | depth > 0 = do
  v1 <- dsbv1 p (depth - 1)
  v1' <- dsbv1 p (depth - 1)
  v2 <- dsbv2 p (depth - 1)
  v2' <- dsbv2 p (depth - 1)
  v3 <- dsbv3 p (depth - 1)
  v4 <- dsbv4 p (depth - 1)
  i <- arbitrary
  oneof
    [ return $ constructUnarySpec UMinusNum v2,
      return $ constructUnarySpec AbsNum v2,
      return $ constructUnarySpec SignumNum v2,
      return $ constructBinarySpec (AddNum @(bv 2)) v2 v2',
      return $ constructBinarySpec TimesNum v2 v2',
      return $ constructBinarySpec (AndBits @(bv 2)) v2 v2',
      return $ constructBinarySpec (OrBits @(bv 2)) v2 v2',
      return $ constructBinarySpec (XorBits @(bv 2)) v2 v2',
      return $ constructUnarySpec (ComplementBits @(bv 2)) v2,
      return $ constructUnarySpec (ShiftBits @(bv 2) i) v2,
      return $ constructUnarySpec (RotateBits @(bv 2) i) v2,
      return $ constructUnarySpec (BVTExtract @0 @2 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @1 @2 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @2 @2 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @0 @2 @3 Proxy) v3,
      return $ constructUnarySpec (BVTExtract @1 @2 @3 Proxy) v3,
      return $ constructUnarySpec (BVTExtract @0 @2 @2 Proxy) v2,
      return $ constructBinarySpec (BVTConcat @1 @1 @2) v1 v1',
      return $ constructUnarySpec (Zext @1 @1 @2 Proxy) v1,
      return $ constructUnarySpec (Sext @1 @1 @2 Proxy) v1
    ]
dsbv2 _ _ = error "Should never be called"

dsbv3 ::
  forall proxy bv.
  ( SupportedBV bv 1,
    SupportedBV bv 2,
    SupportedBV bv 3,
    SupportedBV bv 4,
    UnderlyingBV bv
  ) =>
  proxy bv ->
  Int ->
  Gen (DifferentSizeBVSpec bv 3)
dsbv3 _ 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bv3")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = concSpec . fromInteger <$> arbitrary
   in oneof [r, s]
dsbv3 p depth | depth > 0 = do
  v1 <- dsbv1 p (depth - 1)
  v2 <- dsbv2 p (depth - 1)
  v3 <- dsbv3 p (depth - 1)
  v3' <- dsbv3 p (depth - 1)
  v4 <- dsbv4 p (depth - 1)
  i <- arbitrary
  oneof
    [ return $ constructUnarySpec UMinusNum v3,
      return $ constructUnarySpec AbsNum v3,
      return $ constructUnarySpec SignumNum v3,
      return $ constructBinarySpec (AddNum @(bv 3)) v3 v3',
      return $ constructBinarySpec TimesNum v3 v3',
      return $ constructBinarySpec (AndBits @(bv 3)) v3 v3',
      return $ constructBinarySpec (OrBits @(bv 3)) v3 v3',
      return $ constructBinarySpec (XorBits @(bv 3)) v3 v3',
      return $ constructUnarySpec (ComplementBits @(bv 3)) v3,
      return $ constructUnarySpec (ShiftBits @(bv 3) i) v3,
      return $ constructUnarySpec (RotateBits @(bv 3) i) v3,
      return $ constructUnarySpec (BVTExtract @0 @3 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @1 @3 @4 Proxy) v4,
      return $ constructUnarySpec (BVTExtract @0 @3 @3 Proxy) v3,
      return $ constructBinarySpec (BVTConcat @1 @2 @3) v1 v2,
      return $ constructBinarySpec (BVTConcat @2 @1 @3) v2 v1,
      return $ constructUnarySpec (Zext @2 @1 @3 Proxy) v1,
      return $ constructUnarySpec (Sext @2 @1 @3 Proxy) v1,
      return $ constructUnarySpec (Zext @1 @2 @3 Proxy) v2,
      return $ constructUnarySpec (Sext @1 @2 @3 Proxy) v2
    ]
dsbv3 _ _ = error "Should never be called"

dsbv4 ::
  forall proxy bv.
  ( SupportedBV bv 1,
    SupportedBV bv 2,
    SupportedBV bv 3,
    SupportedBV bv 4,
    UnderlyingBV bv
  ) =>
  proxy bv ->
  Int ->
  Gen (DifferentSizeBVSpec bv 4)
dsbv4 _ 0 =
  let s =
        oneof $
          return . symbSpec . (++ "bv4")
            <$> ["a", "b", "c", "d", "e", "f", "g"]
      r = concSpec . fromInteger <$> arbitrary
   in oneof [r, s]
dsbv4 p depth | depth > 0 = do
  v1 <- dsbv1 p (depth - 1)
  v2 <- dsbv2 p (depth - 1)
  v2' <- dsbv2 p (depth - 1)
  v3 <- dsbv3 p (depth - 1)
  v4 <- dsbv4 p (depth - 1)
  v4' <- dsbv4 p (depth - 1)
  i <- arbitrary
  oneof
    [ return $ constructUnarySpec UMinusNum v4,
      return $ constructUnarySpec AbsNum v4,
      return $ constructUnarySpec SignumNum v4,
      return $ constructBinarySpec (AddNum @(bv 4)) v4 v4',
      return $ constructBinarySpec TimesNum v4 v4',
      return $ constructBinarySpec (AndBits @(bv 4)) v4 v4',
      return $ constructBinarySpec (OrBits @(bv 4)) v4 v4',
      return $ constructBinarySpec (XorBits @(bv 4)) v4 v4',
      return $ constructUnarySpec (ComplementBits @(bv 4)) v4,
      return $ constructUnarySpec (ShiftBits @(bv 4) i) v4,
      return $ constructUnarySpec (RotateBits @(bv 4) i) v4,
      return $ constructUnarySpec (BVTExtract @0 @4 @4 Proxy) v4,
      return $ constructBinarySpec (BVTConcat @1 @3 @4) v1 v3,
      return $ constructBinarySpec (BVTConcat @2 @2 @4) v2 v2',
      return $ constructBinarySpec (BVTConcat @3 @1 @4) v3 v1,
      return $ constructUnarySpec (Zext @3 @1 @4 Proxy) v1,
      return $ constructUnarySpec (Sext @3 @1 @4 Proxy) v1,
      return $ constructUnarySpec (Zext @2 @2 @4 Proxy) v2,
      return $ constructUnarySpec (Sext @2 @2 @4 Proxy) v2,
      return $ constructUnarySpec (Zext @1 @3 @4 Proxy) v3,
      return $ constructUnarySpec (Sext @1 @3 @4 Proxy) v3
    ]
dsbv4 _ _ = error "Should never be called"

instance
  ( SupportedBV bv 1,
    SupportedBV bv 2,
    SupportedBV bv 3,
    SupportedBV bv 4,
    UnderlyingBV bv
  ) =>
  Arbitrary (DifferentSizeBVSpec bv 4)
  where
  arbitrary = sized (dsbv4 Proxy)

data GeneralSpec s = GeneralSpec (Term s) (Term s)

instance (SupportedPrim s) => Show (GeneralSpec s) where
  show (GeneralSpec n r) = "GeneralSpec { no: " ++ pformat n ++ ", re: " ++ pformat r ++ " }"

instance (SupportedPrim s) => TermRewritingSpec (GeneralSpec s) s where
  norewriteVer (GeneralSpec n _) = n
  rewriteVer (GeneralSpec _ r) = r
  wrap = GeneralSpec
  same s = constructBinary Eqv (norewriteVer s) (rewriteVer s)

unop ::
  forall tag a.
  (UnaryOp tag a a) =>
  tag ->
  GeneralSpec a ->
  GeneralSpec a
unop = constructUnarySpec

binop ::
  forall tag a.
  (BinaryOp tag a a a) =>
  tag ->
  GeneralSpec a ->
  GeneralSpec a ->
  GeneralSpec a
binop = constructBinarySpec

times :: (BinaryOp TimesNum a a a, Num a) => GeneralSpec a -> GeneralSpec a -> GeneralSpec a
times = binop TimesNum

add :: forall a. (BinaryOp (AddNum a) a a a, Num a) => GeneralSpec a -> GeneralSpec a -> GeneralSpec a
add = binop (AddNum @a)

uminus :: (UnaryOp UMinusNum a a, Num a) => GeneralSpec a -> GeneralSpec a
uminus = unop UMinusNum

divint :: GeneralSpec Integer -> GeneralSpec Integer -> GeneralSpec Integer
divint = binop DivI

modint :: GeneralSpec Integer -> GeneralSpec Integer -> GeneralSpec Integer
modint = binop ModI

spec :: Spec
spec = do
  let unboundedConfig = UnboundedReasoning SBV.z3 -- {SBV.verbose=True}
  describe "Bool only" $ do
    modifyMaxSize (const 10) $
      prop "Bool only random test" $ \(x :: BoolOnlySpec) -> do
        validateSpec unboundedConfig x
  describe "LIA" $ do
    modifyMaxSize (const 10) $
      prop "LIA random test" $ \(x :: LIAWithBoolSpec) -> do
        validateSpec unboundedConfig x
  describe "Different sized SignedBV" $ do
    modifyMaxSuccess (const 300) $
      modifyMaxSize (const 10) $
        prop "Fixed Sized SignedBV random test" $ \(x :: (DifferentSizeBVSpec BVS.SignedBV 4)) -> do
          validateSpec unboundedConfig x
  describe "Fixed sized SignedBV" $ do
    modifyMaxSuccess (const 300) $
      modifyMaxSize (const 10) $
        prop "Fixed Sized SignedBV random test" $ \(x :: (FixedSizedBVWithBoolSpec BVS.SignedBV)) -> do
          validateSpec unboundedConfig x

  describe "Times on integer" $ do
    it "Times on both concrete" $ do
      traverse_
        (\(x, y) -> validateSpec unboundedConfig $ times @Integer (concSpec x) (concSpec y))
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "Times on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ times @Integer (concSpec x) (symbSpec "a")
            validateSpec unboundedConfig $ times (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
    it "Two times with two concrete combined" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec unboundedConfig $ times @Integer (concSpec x) $ times (concSpec y) (symbSpec "a")
            validateSpec unboundedConfig $ times (concSpec x) $ times (symbSpec "a") (concSpec y)
            validateSpec unboundedConfig $ times (times (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec unboundedConfig $ times (times (symbSpec "a") (concSpec x)) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "Two times with one concrete" $ do
      traverse_
        ( \x -> do
            validateSpec unboundedConfig $ times @Integer (concSpec x) $ times (symbSpec "b") (symbSpec "a")
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
            validateSpec unboundedConfig $ times @Integer (concSpec x) $ add (concSpec y) (symbSpec "a")
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
            validateSpec unboundedConfig $ times @Integer (concSpec x) (uminus $ symbSpec "a")
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
