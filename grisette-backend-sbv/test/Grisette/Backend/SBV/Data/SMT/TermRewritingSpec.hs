{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Grisette.Backend.SBV.Data.SMT.TermRewritingSpec where

import Data.Foldable
import qualified Data.SBV as SBV
import Grisette.Backend.SBV.Data.SMT.Config
import Grisette.Backend.SBV.Data.SMT.Solving ()
import Grisette.Backend.SBV.Data.SMT.TermRewritingGen
import Grisette.Core.Data.Class.Solver
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.SymPrim
import Test.Hspec
import Test.Hspec.QuickCheck

validateSpec :: (TermRewritingSpec a av, Show a, SupportedPrim av) => GrisetteSMTConfig n -> a -> Expectation
validateSpec config a = do
  r <- solveFormula config (Sym $ counterExample a)
  rs <- solveFormula config (Sym $ same a)
  case (r, rs) of
    (Left _, Right _) -> do
      return ()
    (Left _, Left _) -> do
      expectationFailure $ "Bad rewriting with unsolvable formula: " ++ pformat (norewriteVer a) ++ " was rewritten to " ++ pformat (rewriteVer a)
    (Right m, _) -> do
      expectationFailure $ "With model" ++ show m ++ "Bad rewriting: " ++ pformat (norewriteVer a) ++ " was rewritten to " ++ pformat (rewriteVer a)

spec :: Spec
spec = do
  let unboundedConfig = UnboundedReasoning SBV.z3 -- {SBV.verbose=True}
  describe "Bool only" $ do
    modifyMaxSize (const 10) $
      prop "Bool only random test" $ \(x :: BoolOnlySpec) -> do
        validateSpec unboundedConfig x
    it "Regression nested ite with (ite a (ite b c d) e) with b is true" $ do
      validateSpec @BoolOnlySpec unboundedConfig
        (iteSpec
          (symbSpec "yyy" :: BoolOnlySpec)
          (iteSpec
            (orSpec (notSpec (andSpec (symbSpec "dbool") (symbSpec "bbool"))) (symbSpec "bbool") :: BoolOnlySpec)
            (symbSpec "zz")
            (symbSpec "zzz")
            )
          (symbSpec "xxx" :: BoolOnlySpec)
          )
  describe "LIA" $ do
    modifyMaxSize (const 10) $
      prop "LIA random test" $ \(x :: LIAWithBoolSpec) -> do
        validateSpec unboundedConfig x
    it "Regression nested ite with (ite a (ite b c d) e) with b is true" $ do
      validateSpec @BoolOnlySpec unboundedConfig
        (iteSpec
          (symbSpec "yyy" :: BoolOnlySpec)
          (iteSpec
            (orSpec (notSpec (andSpec (symbSpec "dbool") (symbSpec "bbool"))) (symbSpec "bbool") :: BoolOnlySpec)
            (symbSpec "zz")
            (symbSpec "zzz")
            )
          (symbSpec "xxx" :: BoolOnlySpec)
          )
  describe "Different sized SignedBV" $ do
    modifyMaxSuccess (const 300) $
      modifyMaxSize (const 10) $
        prop "Fixed Sized SignedBV random test" $ \(x :: (DifferentSizeBVSpec IntN 4)) -> do
          validateSpec unboundedConfig x
  describe "Fixed sized SignedBV" $ do
    modifyMaxSuccess (const 300) $
      modifyMaxSize (const 10) $
        prop "Fixed Sized SignedBV random test" $ \(x :: (FixedSizedBVWithBoolSpec IntN)) -> do
          validateSpec unboundedConfig x

  describe "timesNumSpec on integer" $ do
    it "times on both concrete" $ do
      traverse_
        (\(x, y) -> validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) (concSpec y))
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "times on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
    it "Two times with two concrete combined" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) $ timesNumSpec (concSpec y) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) $ timesNumSpec (symbSpec "a") (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (timesNumSpec (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (timesNumSpec (symbSpec "a") (concSpec x)) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "Two times with one concrete" $ do
      traverse_
        ( \x -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) $ timesNumSpec (symbSpec "b") (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (symbSpec "b") $ timesNumSpec (symbSpec "a") (concSpec x)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (symbSpec "b") $ timesNumSpec (concSpec x) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (timesNumSpec (concSpec x) (symbSpec "a")) (symbSpec "b")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (timesNumSpec (symbSpec "a") (concSpec x)) (symbSpec "b")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (timesNumSpec (symbSpec "a") (symbSpec "b")) (concSpec x)
        )
        [-3 .. 3]
    it "times and add with two concretes combined" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) $ addNumSpec (concSpec y) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) $ addNumSpec (symbSpec "a") (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (addNumSpec (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (addNumSpec (symbSpec "a") (concSpec x)) (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ addNumSpec (concSpec x) $ timesNumSpec (concSpec y) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ addNumSpec (concSpec x) $ timesNumSpec (symbSpec "a") (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ addNumSpec (timesNumSpec (concSpec x) (symbSpec "a")) (concSpec y)
            validateSpec @(GeneralSpec Integer) unboundedConfig $ addNumSpec (timesNumSpec (symbSpec "a") (concSpec x)) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "times concrete with uminusNumSpec symbolic" $ do
      traverse_
        ( \x -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (concSpec x) (uminusNumSpec $ symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ timesNumSpec (uminusNumSpec $ symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
  describe "DivI" $ do
    it "DivI on concrete" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ divIntegerSpec (concSpec x) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "DivI on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ divIntegerSpec (concSpec x) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ divIntegerSpec (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
  describe "ModI" $ do
    it "ModI on concrete" $ do
      traverse_
        ( \(x, y) -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ modIntegerSpec (concSpec x) (concSpec y)
        )
        [(i, j) | i <- [-3 .. 3], j <- [-3 .. 3]]
    it "ModI on single concrete" $ do
      traverse_
        ( \x -> do
            validateSpec @(GeneralSpec Integer) unboundedConfig $ modIntegerSpec (concSpec x) (symbSpec "a")
            validateSpec @(GeneralSpec Integer) unboundedConfig $ modIntegerSpec (symbSpec "a") (concSpec x)
        )
        [-3 .. 3]
