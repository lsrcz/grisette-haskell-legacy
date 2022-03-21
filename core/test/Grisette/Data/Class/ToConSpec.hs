module Grisette.Data.Class.ToConSpec where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import qualified Data.ByteString.Char8 as C
import Data.Foldable
import Data.Functor.Sum
import Grisette.Data.Class.ToCon
import Test.Hspec
import Test.Hspec.QuickCheck
import Utils.SBool

toConForConcreteProp :: (ToCon v v, Show v, Eq v) => v -> Expectation
toConForConcreteProp v = toCon v `shouldBe` Just v

spec :: Spec
spec = do
  describe "ToCon for common types" $ do
    describe "ToCon for SBool" $ do
      it "ToCon for concrete SBool should work" $ do
        let bools :: [Bool] = [True, False]
        traverse_ (\v -> toCon (CBool v) `shouldBe` Just v) bools
      it "ToCon for symbolic SBool to symbolic SBool should work" $ do
        let sbools :: [SBool] =
              [ CBool True,
                SSBool "a",
                ISBool 1 "a",
                And (SSBool "a") (SSBool "b"),
                Or (SSBool "a") (SSBool "b"),
                Not (SSBool "a"),
                Equal (SSBool "a") (SSBool "b"),
                ITE (SSBool "a") (SSBool "b") (SSBool "c")
              ]
        traverse_ (\v -> toCon v `shouldBe` Just v) sbools
      it "ToCon for symbolic SBool should work" $ do
        let sbools :: [SBool] =
              [ SSBool "a",
                ISBool 1 "a",
                And (SSBool "a") (SSBool "b"),
                Or (SSBool "a") (SSBool "b"),
                Not (SSBool "a"),
                Equal (SSBool "a") (SSBool "b"),
                ITE (SSBool "a") (SSBool "b") (SSBool "c")
              ]
        traverse_ (\v -> toCon v `shouldBe` (Nothing :: Maybe Bool)) sbools
    describe "ToCon for Bool" $ do
      prop "ToCon for Bool should always be identical to Just" $ toConForConcreteProp @Bool
    describe "ToCon for Integer" $ do
      prop "ToCon for Integer should always be identical to Just" $ toConForConcreteProp @Integer
    describe "ToCon for Char" $ do
      prop "ToCon for Char should always be identical to Just" $ toConForConcreteProp @Char
    describe "ToCon for ()" $ do
      prop "ToCon for () should always be identical to Just" $ toConForConcreteProp @()
    describe "ToCon for ByteString" $ do
      prop "ToCon for ByteString should always be identical to Just" $
        \(v :: String) -> toConForConcreteProp (C.pack v)
    describe "ToCon for List" $ do
      prop "ToCon for concrete List should always be identical to Just" $ toConForConcreteProp @[Integer]
      it "ToCon for general List should work" $ do
        toCon ([] :: [SBool]) `shouldBe` (Just [] :: Maybe [Bool])
        toCon ([CBool True] :: [SBool]) `shouldBe` (Just [True] :: Maybe [Bool])
        toCon ([SSBool "a"] :: [SBool]) `shouldBe` (Nothing :: Maybe [Bool])
        toCon ([CBool True, CBool False] :: [SBool]) `shouldBe` (Just [True, False] :: Maybe [Bool])
        toCon ([CBool True, SSBool "a"] :: [SBool]) `shouldBe` (Nothing :: Maybe [Bool])
    describe "ToCon for Maybe" $ do
      prop "ToCon for concrete Maybe should always be identical to Just" $ toConForConcreteProp @(Maybe Integer)
      it "ToCon for general Maybe should work" $ do
        toCon (Nothing :: Maybe SBool) `shouldBe` (Just Nothing :: Maybe (Maybe Bool))
        toCon (Just (CBool True) :: Maybe SBool) `shouldBe` (Just (Just True) :: Maybe (Maybe Bool))
        toCon (Just (SSBool "a") :: Maybe SBool) `shouldBe` (Nothing :: Maybe (Maybe Bool))
    describe "ToCon for Either" $ do
      prop "ToCon for concrete Either should always be identical to Just" $ toConForConcreteProp @(Either Integer Integer)
      it "ToCon for general Either should work" $ do
        toCon (Left (CBool True) :: Either SBool SBool) `shouldBe` (Just (Left True) :: Maybe (Either Bool Bool))
        toCon (Right (CBool True) :: Either SBool SBool) `shouldBe` (Just (Right True) :: Maybe (Either Bool Bool))
        toCon (Left (SSBool "a") :: Either SBool SBool) `shouldBe` (Nothing :: Maybe (Either Bool Bool))
        toCon (Right (SSBool "a") :: Either SBool SBool) `shouldBe` (Nothing :: Maybe (Either Bool Bool))
    describe "ToCon for MaybeT" $ do
      prop "ToCon for concrete MaybeT should always be identical to Just" $
        \(v :: Maybe (Maybe Integer)) -> toConForConcreteProp (MaybeT v)
      it "ToCon for general MaybeT should work" $ do
        toCon (MaybeT Nothing :: MaybeT Maybe SBool) `shouldBe` (Just $ MaybeT Nothing :: Maybe (MaybeT Maybe Bool))
        toCon (MaybeT $ Just Nothing :: MaybeT Maybe SBool)
          `shouldBe` (Just $ MaybeT $ Just Nothing :: Maybe (MaybeT Maybe Bool))
        toCon (MaybeT $ Just $ Just $ CBool True :: MaybeT Maybe SBool)
          `shouldBe` (Just $ MaybeT $ Just $ Just True :: Maybe (MaybeT Maybe Bool))
        toCon (MaybeT $ Just $ Just $ SSBool "a" :: MaybeT Maybe SBool)
          `shouldBe` (Nothing :: Maybe (MaybeT Maybe Bool))
    describe "ToCon for ExceptT" $ do
      prop "ToCon for concrete ExceptT should always be identical to Just" $
        \(v :: Maybe (Either Integer Integer)) -> toConForConcreteProp (ExceptT v)
      it "ToCon for general ExceptT should work" $ do
        toCon (ExceptT Nothing :: ExceptT SBool Maybe SBool)
          `shouldBe` (Just $ ExceptT Nothing :: Maybe (ExceptT Bool Maybe Bool))
        toCon (ExceptT $ Just $ Left $ CBool True :: ExceptT SBool Maybe SBool)
          `shouldBe` (Just $ ExceptT $ Just $ Left True :: Maybe (ExceptT Bool Maybe Bool))
        toCon (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` (Nothing :: Maybe (ExceptT Bool Maybe Bool))
        toCon (ExceptT $ Just $ Right $ CBool True :: ExceptT SBool Maybe SBool)
          `shouldBe` (Just $ ExceptT $ Just $ Right True :: Maybe (ExceptT Bool Maybe Bool))
        toCon (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` (Nothing :: Maybe (ExceptT Bool Maybe Bool))
    describe "ToCon for (,)" $ do
      prop "ToCon for concrete (,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer)
      it "ToCon for generic (,) should work" $ do
        toCon (CBool True, CBool False) `shouldBe` Just (True, False)
        toCon (CBool True, SSBool "a") `shouldBe` (Nothing :: Maybe (Bool, Bool))
    describe "ToCon for (,,)" $ do
      prop "ToCon for concrete (,,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer, Integer)
      it "ToCon for generic (,,) should work" $ do
        toCon (CBool False, CBool True, CBool False) `shouldBe` Just (False, True, False)
        toCon (CBool False, CBool True, SSBool "a") `shouldBe` (Nothing :: Maybe (Bool, Bool, Bool))
    describe "ToCon for (,,,)" $ do
      prop "ToCon for concrete (,,,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer, Integer, Integer)
      it "ToCon for generic (,,,) should work" $ do
        toCon (CBool True, CBool False, CBool True, CBool False) `shouldBe` Just (True, False, True, False)
        toCon (CBool True, CBool False, CBool True, SSBool "a") `shouldBe` (Nothing :: Maybe (Bool, Bool, Bool, Bool))
    describe "ToCon for (,,,,)" $ do
      prop "ToCon for concrete (,,,,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer, Integer, Integer, Integer)
      it "ToCon for generic (,,,,) should work" $ do
        toCon (CBool False, CBool True, CBool False, CBool True, CBool False)
          `shouldBe` Just (False, True, False, True, False)
        toCon (CBool False, CBool True, CBool False, CBool True, SSBool "a")
          `shouldBe` (Nothing :: Maybe (Bool, Bool, Bool, Bool, Bool))
    describe "ToCon for (,,,,,)" $ do
      prop "ToCon for concrete (,,,,,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer, Integer, Integer, Integer, Integer)
      it "ToCon for generic (,,,,,) should work" $ do
        toCon (CBool True, CBool False, CBool True, CBool False, CBool True, CBool False)
          `shouldBe` Just (True, False, True, False, True, False)
        toCon (CBool True, CBool False, CBool True, CBool False, CBool True, SSBool "a")
          `shouldBe` (Nothing :: Maybe (Bool, Bool, Bool, Bool, Bool, Bool))
    describe "ToCon for (,,,,,,)" $ do
      prop "ToCon for concrete (,,,,,,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer, Integer, Integer, Integer, Integer, Integer)
      it "ToCon for generic (,,,,,,) should work" $ do
        toCon (CBool False, CBool True, CBool False, CBool True, CBool False, CBool True, CBool False)
          `shouldBe` Just (False, True, False, True, False, True, False)
        toCon (CBool False, CBool True, CBool False, CBool True, CBool False, CBool True, SSBool "a")
          `shouldBe` (Nothing :: Maybe (Bool, Bool, Bool, Bool, Bool, Bool, Bool))
    describe "ToCon for (,,,,,,,)" $ do
      prop "ToCon for concrete (,,,,,,,) should always be identical to Just" $
        toConForConcreteProp @(Integer, Integer, Integer, Integer, Integer, Integer, Integer, Integer)
      it "ToCon for generic (,,,,,,,) should work" $ do
        toCon (CBool True, CBool False, CBool True, CBool False, CBool True, CBool False, CBool True, CBool False)
          `shouldBe` Just (True, False, True, False, True, False, True, False)
        toCon (CBool True, CBool False, CBool True, CBool False, CBool True, CBool False, CBool True, SSBool "a")
          `shouldBe` (Nothing :: Maybe (Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool))
    describe "ToCon for Sum" $ do
      prop "ToCon for concrete Sum should always be identical to Just" $
        \(v :: Either (Maybe Integer) (Maybe Integer)) -> toConForConcreteProp $ case v of
          Left x -> InL x
          Right x -> InR x
      it "ToCon for generic Sum should work" $ do
        toCon (InL (Just (CBool True)) :: Sum Maybe (Either SBool) SBool) `shouldBe`
          (Just (InL (Just True)) :: Maybe (Sum Maybe (Either Bool) Bool))
        toCon (InL (Just (SSBool "a")) :: Sum Maybe (Either SBool) SBool) `shouldBe`
          (Nothing :: Maybe (Sum Maybe (Either Bool) Bool))
        toCon (InR (Left (CBool True)) :: Sum Maybe (Either SBool) SBool) `shouldBe`
          (Just (InR (Left True)) :: Maybe (Sum Maybe (Either Bool) Bool))
        toCon (InR (Right (CBool True)) :: Sum Maybe (Either SBool) SBool) `shouldBe`
          (Just (InR (Right True)) :: Maybe (Sum Maybe (Either Bool) Bool))
        toCon (InR (Left (SSBool "a")) :: Sum Maybe (Either SBool) SBool) `shouldBe`
          (Nothing :: Maybe (Sum Maybe (Either Bool) Bool))
        toCon (InR (Right (SSBool "a")) :: Sum Maybe (Either SBool) SBool) `shouldBe`
          (Nothing :: Maybe (Sum Maybe (Either Bool) Bool))
