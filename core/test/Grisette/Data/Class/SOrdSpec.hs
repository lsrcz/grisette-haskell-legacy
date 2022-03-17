{-# LANGUAGE OverloadedStrings #-}
module Grisette.Data.Class.SOrdSpec where

import Grisette.Data.Class.Bool
import Grisette.Data.Class.SOrd
import Test.Hspec
import Test.Hspec.QuickCheck
import Utils.SBool
import qualified Data.ByteString as B
import Data.Foldable
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase

concreteOrdOkProp :: (SOrd SBool a, Ord a) => (a, a) -> Expectation
concreteOrdOkProp (i, j) = do
  i <=~ j `shouldBe` CBool (i <= j)
  i <~ j `shouldBe` CBool (i < j)
  i >=~ j `shouldBe` CBool (i >= j)
  i >~ j `shouldBe` CBool (i > j)
  symCompare i j `shouldBe` (mrgReturn $ compare i j :: UnionMBase SBool Ordering)

spec :: Spec
spec = do
  describe "SOrd for common types" $ do
    it "SOrd for SBool" $ do
      SSBool "a" <=~ SSBool "b" `shouldBe` Or (Not (SSBool "a")) (SSBool "b")
      SSBool "a" <~ SSBool "b" `shouldBe` And (Not (SSBool "a")) (SSBool "b")
      SSBool "a" >=~ SSBool "b" `shouldBe` Or (SSBool "a") (Not (SSBool "b"))
      SSBool "a" >~ SSBool "b" `shouldBe` And (SSBool "a") (Not (SSBool "b"))
      symCompare (SSBool "a") (SSBool "b") `shouldBe`
        (mrgIf (And (Not (SSBool "a")) (SSBool "b"))
          (mrgReturn LT)
          (mrgIf (Equal (SSBool "a") (SSBool "b"))
            (mrgReturn EQ)
            (mrgReturn GT)) :: UnionMBase SBool Ordering)
    prop "SOrd for Bool" (concreteOrdOkProp @Bool)
    prop "SOrd for Integer" (concreteOrdOkProp @Integer)
    prop "SOrd for Char" (concreteOrdOkProp @Char)
    prop "SOrd for concrete List" (concreteOrdOkProp @[Integer])
    prop "SOrd for concrete String" (concreteOrdOkProp @String)
    it "SOrd for List" $ do
      ([] :: [SBool]) <=~ [] `shouldBe` CBool True
      ([] :: [SBool]) <~ [] `shouldBe` CBool False
      ([] :: [SBool]) >=~ [] `shouldBe` CBool True
      ([] :: [SBool]) >~ [] `shouldBe` CBool False
      ([] :: [SBool]) `symCompare` [] `shouldBe` (mrgReturn EQ :: UnionMBase SBool Ordering)
      [] <=~ [SSBool "a"] `shouldBe` CBool True
      [] <~ [SSBool "a"] `shouldBe` CBool True
      [] >=~ [SSBool "a"] `shouldBe` CBool False
      [] >~ [SSBool "a"] `shouldBe` CBool False
      [] `symCompare` [SSBool "a"] `shouldBe` (mrgReturn LT :: UnionMBase SBool Ordering)
      [SSBool "a"] <=~ [] `shouldBe` CBool False
      [SSBool "a"] <~ [] `shouldBe` CBool False
      [SSBool "a"] >=~ [] `shouldBe` CBool True
      [SSBool "a"] >~ [] `shouldBe` CBool True
      [SSBool "a"] `symCompare` [] `shouldBe` (mrgReturn GT :: UnionMBase SBool Ordering)

      [SSBool "a", SSBool "b"] <=~ [SSBool "c"]
        `shouldBe` (SSBool "a" <~ SSBool "c" :: SBool)
      [SSBool "a", SSBool "b"] <~ [SSBool "c"]
        `shouldBe` (SSBool "a" <~ SSBool "c" :: SBool)
      [SSBool "a", SSBool "b"] >=~ [SSBool "c"]
        `shouldBe` ((SSBool "a" >~ SSBool "c") ||~ (SSBool "a" ==~ SSBool "c") :: SBool)
      [SSBool "a", SSBool "b"] >~ [SSBool "c"]
        `shouldBe` ((SSBool "a" >~ SSBool "c") ||~ (SSBool "a" ==~ SSBool "c") :: SBool)
      [SSBool "a"] `symCompare` [SSBool "b"] `shouldBe` (SSBool "a" `symCompare` SSBool "b" :: UnionMBase SBool Ordering)

      [SSBool "a"] <=~ [SSBool "b", SSBool "c"]
        `shouldBe` ((SSBool "a" <~ SSBool "b") ||~ (SSBool "a" ==~ SSBool "b") :: SBool)
      [SSBool "a"] <~ [SSBool "b", SSBool "c"]
        `shouldBe` ((SSBool "a" <~ SSBool "b") ||~ (SSBool "a" ==~ SSBool "b") :: SBool)
      [SSBool "a"] >=~ [SSBool "b", SSBool "c"]
        `shouldBe` (SSBool "a" >~ SSBool "b" :: SBool)
      [SSBool "a"] >~ [SSBool "b", SSBool "c"]
        `shouldBe` (SSBool "a" >~ SSBool "b" :: SBool)
      [SSBool "a"] `symCompare` [SSBool "b", SSBool "c"] `shouldBe`
        (mrgIf (SSBool "a" <~ SSBool "b") (mrgReturn LT)
          (mrgIf (SSBool "a" ==~ SSBool "b") (mrgReturn LT) (mrgReturn GT)) :: UnionMBase SBool Ordering)

      [SSBool "a", SSBool "b"] <=~ [SSBool "c", SSBool "d"]
        `shouldBe` ( (SSBool "a" <~ SSBool "c")
                       ||~ ( SSBool "a" ==~ SSBool "c"
                               &&~ ((SSBool "b" <~ SSBool "d") ||~ (SSBool "b" ==~ SSBool "d"))
                           ) ::
                       SBool
                   )
      [SSBool "a", SSBool "b"] <~ [SSBool "c", SSBool "d"]
        `shouldBe` ( (SSBool "a" <~ SSBool "c")
                       ||~ ( SSBool "a" ==~ SSBool "c"
                               &&~ (SSBool "b" <~ SSBool "d")
                           ) ::
                       SBool
                   )
      [SSBool "a", SSBool "b"] >=~ [SSBool "c", SSBool "d"]
        `shouldBe` ( (SSBool "a" >~ SSBool "c")
                       ||~ ( SSBool "a" ==~ SSBool "c"
                               &&~ ((SSBool "b" >~ SSBool "d") ||~ (SSBool "b" ==~ SSBool "d"))
                           ) ::
                       SBool
                   )
      [SSBool "a", SSBool "b"] >~ [SSBool "c", SSBool "d"]
        `shouldBe` ( (SSBool "a" >~ SSBool "c")
                       ||~ ( SSBool "a" ==~ SSBool "c"
                               &&~ (SSBool "b" >~ SSBool "d")
                           ) ::
                       SBool
                   )
      [SSBool "a", SSBool "b"] `symCompare` [SSBool "c", SSBool "d"] `shouldBe`
        (mrgIf (SSBool "a" <~ SSBool "c")
          (mrgReturn LT)
          (mrgIf (SSBool "a" ==~ SSBool "c")
            (SSBool "b" `symCompare` SSBool "d")
            (mrgReturn GT)) :: UnionMBase SBool Ordering)
    prop "SOrd for concrete Maybe" (concreteOrdOkProp @(Maybe Integer))
    it "SOrd for Maybe" $ do
      (Nothing :: Maybe SBool) <=~ Nothing `shouldBe` CBool True
      (Nothing :: Maybe SBool) <~ Nothing `shouldBe` CBool False
      (Nothing :: Maybe SBool) >=~ Nothing `shouldBe` CBool True
      (Nothing :: Maybe SBool) >~ Nothing `shouldBe` CBool False
      (Nothing :: Maybe SBool) `symCompare` Nothing `shouldBe` (mrgReturn EQ :: UnionMBase SBool Ordering)
      Nothing <=~ Just (SSBool "a") `shouldBe` CBool True
      Nothing <~ Just (SSBool "a") `shouldBe` CBool True
      Nothing >=~ Just (SSBool "a") `shouldBe` CBool False
      Nothing >~ Just (SSBool "a") `shouldBe` CBool False
      Nothing `symCompare` Just (SSBool "a") `shouldBe` (mrgReturn LT :: UnionMBase SBool Ordering)
      Just (SSBool "a") <=~ Nothing `shouldBe` CBool False
      Just (SSBool "a") <~ Nothing `shouldBe` CBool False
      Just (SSBool "a") >=~ Nothing `shouldBe` CBool True
      Just (SSBool "a") >~ Nothing `shouldBe` CBool True
      Just (SSBool "a") `symCompare` Nothing `shouldBe` (mrgReturn GT :: UnionMBase SBool Ordering)
      Just (SSBool "a") <=~ Just (SSBool "b") `shouldBe` (SSBool "a" <=~ SSBool "b" :: SBool)
      Just (SSBool "a") <~ Just (SSBool "b") `shouldBe` (SSBool "a" <~ SSBool "b" :: SBool)
      Just (SSBool "a") >=~ Just (SSBool "b") `shouldBe` (SSBool "a" >=~ SSBool "b" :: SBool)
      Just (SSBool "a") >~ Just (SSBool "b") `shouldBe` (SSBool "a" >~ SSBool "b" :: SBool)
      Just (SSBool "a") `symCompare` Just (SSBool "b") `shouldBe`
        (SSBool "a" `symCompare` SSBool "b" :: UnionMBase SBool Ordering)
    prop "SOrd for concrete Either" (concreteOrdOkProp @(Either Integer Integer))
    it "SOrd for Either" $ do
      (Left (SSBool "a") :: Either SBool SBool) <=~ Left (SSBool "b") `shouldBe` (SSBool "a" <=~ SSBool "b" :: SBool)
      (Left (SSBool "a") :: Either SBool SBool) <~ Left (SSBool "b") `shouldBe` (SSBool "a" <~ SSBool "b" :: SBool)
      (Left (SSBool "a") :: Either SBool SBool) >=~ Left (SSBool "b") `shouldBe` (SSBool "a" >=~ SSBool "b" :: SBool)
      (Left (SSBool "a") :: Either SBool SBool) >~ Left (SSBool "b") `shouldBe` (SSBool "a" >~ SSBool "b" :: SBool)
      (Left (SSBool "a") :: Either SBool SBool) `symCompare` Left (SSBool "b") `shouldBe`
        (SSBool "a" `symCompare` SSBool "b" :: UnionMBase SBool Ordering)
      (Left (SSBool "a") :: Either SBool SBool) <=~ Right (SSBool "b") `shouldBe` CBool True
      (Left (SSBool "a") :: Either SBool SBool) <~ Right (SSBool "b") `shouldBe` CBool True
      (Left (SSBool "a") :: Either SBool SBool) >=~ Right (SSBool "b") `shouldBe` CBool False
      (Left (SSBool "a") :: Either SBool SBool) >~ Right (SSBool "b") `shouldBe` CBool False
      (Left (SSBool "a") :: Either SBool SBool) `symCompare` Right (SSBool "b") `shouldBe`
        (mrgReturn LT :: UnionMBase SBool Ordering)
      (Right (SSBool "a") :: Either SBool SBool) <=~ Left (SSBool "b") `shouldBe` CBool False
      (Right (SSBool "a") :: Either SBool SBool) <~ Left (SSBool "b") `shouldBe` CBool False
      (Right (SSBool "a") :: Either SBool SBool) >=~ Left (SSBool "b") `shouldBe` CBool True
      (Right (SSBool "a") :: Either SBool SBool) >~ Left (SSBool "b") `shouldBe` CBool True
      (Right (SSBool "a") :: Either SBool SBool) `symCompare` Left (SSBool "b") `shouldBe`
        (mrgReturn GT :: UnionMBase SBool Ordering)
      (Right (SSBool "a") :: Either SBool SBool) <=~ Right (SSBool "b") `shouldBe` (SSBool "a" <=~ SSBool "b" :: SBool)
      (Right (SSBool "a") :: Either SBool SBool) <~ Right (SSBool "b") `shouldBe` (SSBool "a" <~ SSBool "b" :: SBool)
      (Right (SSBool "a") :: Either SBool SBool) >=~ Right (SSBool "b") `shouldBe` (SSBool "a" >=~ SSBool "b" :: SBool)
      (Right (SSBool "a") :: Either SBool SBool) >~ Right (SSBool "b") `shouldBe` (SSBool "a" >~ SSBool "b" :: SBool)
      (Right (SSBool "a") :: Either SBool SBool) `symCompare` Right (SSBool "b") `shouldBe`
        (SSBool "a" `symCompare` SSBool "b" :: UnionMBase SBool Ordering)
    prop "SOrd for concrete (,)" (concreteOrdOkProp @(Integer, Integer))
    it "SOrd for ByteString" $ do
      let bytestrings :: [B.ByteString] = ["", "a", "b", "ab", "ba", "aa", "bb"]
      traverse_ concreteOrdOkProp [(x, y) | x <- bytestrings, y <- bytestrings]
      
