module Grisette.Data.UnionBaseSpec where

import GHC.Generics
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.UnionBase
import Test.Hspec
import Utils.SBool

data TripleSum a b c = TS1 a | TS2 b | TS3 c deriving (Show, Eq, Generic)

instance (SymBoolOp bool, Mergeable bool a, Mergeable bool b, Mergeable bool c) => Mergeable bool (TripleSum a b c)

spec :: Spec
spec = do
  describe "guardWithLeftMost" $ do
    it "guardWithLeftMost should maintain left most info" $ do
      guardWithLeftMost False (SSBool "a") (Single (1 :: Integer)) (Single 2)
        `shouldBe` Guard 1 False (SSBool "a") (Single 1) (Single 2)
      guardWithLeftMost
        True
        (SSBool "a")
        (Guard 1 True (SSBool "b") (Single (1 :: Integer)) (Single 2))
        (Guard 3 True (SSBool "c") (Single 3) (Single 4))
        `shouldBe` Guard
          1
          True
          (SSBool "a")
          (Guard 1 True (SSBool "b") (Single (1 :: Integer)) (Single 2))
          (Guard 3 True (SSBool "c") (Single 3) (Single 4))
  describe "guardWithStrategy" $ do
    it "guardWithStrategy with concrete condition" $ do
      guardWithStrategy mergeStrategy (CBool True) (Single (1 :: Integer)) (Single 2) `shouldBe` Single 1
      guardWithStrategy mergeStrategy (CBool False) (Single (1 :: Integer)) (Single 2) `shouldBe` Single 2
    it "guardWithStrategy with condition equal to sub conditions" $ do
      let a = guardWithStrategy mergeStrategy (SSBool "a") (Single (1 :: Integer)) (Single 2)
      guardWithStrategy mergeStrategy (SSBool "a") a (Single 3)
        `shouldBe` Guard 1 True (SSBool "a") (Single 1) (Single 3)
      guardWithStrategy mergeStrategy (SSBool "a") (Single 0) a
        `shouldBe` Guard 0 True (SSBool "a") (Single 0) (Single 2)
    it "guardWithStrategy with simple mergeables" $ do
      guardWithStrategy mergeStrategy (SSBool "a") (Single (SSBool "b")) (Single (SSBool "c"))
        `shouldBe` Single (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    describe "guardWithStrategy with ordered mergeables" $ do
      describe "guardWithStrategy on Single/Single" $ do
        it "guardWithStrategy on Single/Single with idxt < idxf" $ do
          guardWithStrategy mergeStrategy (SSBool "a") (Single (1 :: Integer)) (Single 2)
            `shouldBe` Guard 1 True (SSBool "a") (Single 1) (Single 2)
          guardWithStrategy mergeStrategy (SSBool "a") (Single Nothing) (Single (Just (2 :: Integer)))
            `shouldBe` Guard Nothing True (SSBool "a") (Single Nothing) (Single (Just 2))
        describe "guardWithStrategy on Single/Single with idxt == idxf" $ do
          it "guardWithStrategy on Single/Single with idxt == idxf as terminal" $ do
            guardWithStrategy mergeStrategy (SSBool "a") (Single (1 :: Integer)) (Single 1)
              `shouldBe` Single 1
            guardWithStrategy mergeStrategy (SSBool "a") (Single (Just (SSBool "b"))) (Single (Just (SSBool "c")))
              `shouldBe` Single (Just (ITE (SSBool "a") (SSBool "b") (SSBool "c")))
          it "guardWithStrategy on Single/Single with idxt == idxf but not terminal" $ do
            guardWithStrategy mergeStrategy (SSBool "a") (Single (Just (1 :: Integer))) (Single (Just (2 :: Integer)))
              `shouldBe` Guard (Just 1) True (SSBool "a") (Single $ Just 1) (Single (Just 2))
            guardWithStrategy
              mergeStrategy
              (SSBool "a")
              (Single $ Just $ Just $ SSBool "b")
              (Single $ Just $ Just $ SSBool "c")
              `shouldBe` Single (Just (Just (ITE (SSBool "a") (SSBool "b") (SSBool "c"))))
        it "guardWithStrategy on Single/Single with idxt > idxf" $ do
          guardWithStrategy mergeStrategy (SSBool "a") (Single (2 :: Integer)) (Single 1)
            `shouldBe` Guard 1 True (Not $ SSBool "a") (Single 1) (Single 2)
          guardWithStrategy mergeStrategy (SSBool "a") (Single (Just (2 :: Integer))) (Single Nothing)
            `shouldBe` Guard Nothing True (Not $ SSBool "a") (Single Nothing) (Single (Just 2))
      describe "guardWithStrategy on Single/Guard" $ do
        describe "guardWithStrategy on Single/Guard degenerate to Single/Single when idxft == idxff" $ do
          it "guardWithStrategy on Single/Guard for degenerated case with idxt < idxf" $ do
            let x =
                  guardWithStrategy
                    mergeStrategy
                    (SSBool "a")
                    (Single (Just (1 :: Integer)))
                    (Single (Just (2 :: Integer)))
            guardWithStrategy mergeStrategy (SSBool "b") (Single Nothing) x
              `shouldBe` Guard
                Nothing
                True
                (SSBool "b")
                (Single Nothing)
                (Guard (Just 1) True (SSBool "a") (Single $ Just 1) (Single (Just 2)))
          it "guardWithStrategy on Single/Guard for degenerated case with idxt == idxf" $ do
            let x =
                  guardWithStrategy
                    mergeStrategy
                    (SSBool "a")
                    (Single (Just (1 :: Integer)))
                    (Single (Just (3 :: Integer)))
            guardWithStrategy mergeStrategy (SSBool "b") (Single $ Just 0) x
              `shouldBe` Guard
                (Just 0)
                True
                (SSBool "b")
                (Single $ Just 0)
                (Guard (Just 1) True (SSBool "a") (Single $ Just 1) (Single (Just 3)))
            guardWithStrategy mergeStrategy (SSBool "b") (Single $ Just 1) x
              `shouldBe` Guard (Just 1) True (Or (SSBool "b") (SSBool "a")) (Single $ Just 1) (Single (Just 3))
            guardWithStrategy mergeStrategy (SSBool "b") (Single $ Just 2) x
              `shouldBe` Guard
                (Just 1)
                True
                (And (Not (SSBool "b")) (SSBool "a"))
                (Single $ Just 1)
                (Guard (Just 2) True (SSBool "b") (Single $ Just 2) (Single $ Just 3))
            guardWithStrategy mergeStrategy (SSBool "b") (Single $ Just 3) x
              `shouldBe` Guard (Just 1) True (And (Not (SSBool "b")) (SSBool "a")) (Single $ Just 1) (Single (Just 3))
            guardWithStrategy mergeStrategy (SSBool "b") (Single $ Just 4) x
              `shouldBe` Guard
                (Just 1)
                True
                (And (Not (SSBool "b")) (SSBool "a"))
                (Single $ Just 1)
                (Guard (Just 3) True (Not $ SSBool "b") (Single $ Just 3) (Single $ Just 4))
          it "guardWithStrategy on Single/Guard for degenerated case with idxt > idxf" $ do
            let x =
                  guardWithStrategy
                    mergeStrategy
                    (SSBool "a")
                    (Single (Left (1 :: Integer)))
                    (Single (Left (2 :: Integer)))
            guardWithStrategy mergeStrategy (SSBool "b") (Single $ Right (1 :: Integer)) x
              `shouldBe` Guard
                (Left 1)
                True
                (Not $ SSBool "b")
                (Guard (Left 1) True (SSBool "a") (Single $ Left 1) (Single (Left 2)))
                (Single $ Right 1)
        it "guardWithStrategy on Single/Guard for idxt < idxft" $ do
          let x =
                guardWithStrategy
                  mergeStrategy
                  (SSBool "a")
                  (Single (1 :: Integer))
                  (Single (3 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "b") (Single 0) x
            `shouldBe` Guard 0 True (SSBool "b") (Single 0) (Guard 1 True (SSBool "a") (Single 1) (Single 3))
        it "guardWithStrategy on Single/Guard for idxt == idxft" $ do
          let x =
                guardWithStrategy
                  mergeStrategy
                  (SSBool "a")
                  (Single $ Left (1 :: Integer))
                  (Single $ Right (3 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "b") (Single $ Left 0) x
            `shouldBe` Guard
              (Left 0)
              True
              (Or (SSBool "b") (SSBool "a"))
              (Guard (Left 0) True (SSBool "b") (Single $ Left 0) (Single $ Left 1))
              (Single $ Right 3)
        it "guardWithStrategy on Single/Guard for idxt > idxft" $ do
          let x =
                guardWithStrategy
                  mergeStrategy
                  (SSBool "a")
                  (Single $ Left (1 :: Integer))
                  (Single $ Right (3 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "b") (Single $ Right 0) x
            `shouldBe` Guard
              (Left 1)
              True
              (And (Not (SSBool "b")) (SSBool "a"))
              (Single $ Left 1)
              (Guard (Right 0) True (SSBool "b") (Single $ Right 0) (Single $ Right 3))
      describe "guardWithStrategy on Guard/Single" $ do
        describe "guardWithStrategy on Guard/Single degenerate to Single/Single when idxtt == idxtf" $ do
          it "guardWithStrategy on Single/Guard for degenerated case with idxt < idxf" $ do
            let x =
                  guardWithStrategy
                    mergeStrategy
                    (SSBool "a")
                    (Single (Left (1 :: Integer)))
                    (Single (Left (2 :: Integer)))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Right (2 :: Integer))
              `shouldBe` Guard
                (Left 1)
                True
                (SSBool "b")
                (Guard (Left 1) True (SSBool "a") (Single $ Left 1) (Single (Left 2)))
                (Single $ Right 2)
          it "guardWithStrategy on Single/Guard for degenerated case with idxt == idxf" $ do
            let x =
                  guardWithStrategy
                    mergeStrategy
                    (SSBool "a")
                    (Single (Just (1 :: Integer)))
                    (Single (Just (3 :: Integer)))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Just 0)
              `shouldBe` Guard
                (Just 0)
                True
                (Not (SSBool "b"))
                (Single $ Just 0)
                (Guard (Just 1) True (SSBool "a") (Single $ Just 1) (Single (Just 3)))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Just 1)
              `shouldBe` Guard (Just 1) True (Or (Not $ SSBool "b") (SSBool "a")) (Single $ Just 1) (Single (Just 3))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Just 2)
              `shouldBe` Guard
                (Just 1)
                True
                (And (SSBool "b") (SSBool "a"))
                (Single $ Just 1)
                (Guard (Just 2) True (Not $ SSBool "b") (Single $ Just 2) (Single $ Just 3))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Just 3)
              `shouldBe` Guard (Just 1) True (And (SSBool "b") (SSBool "a")) (Single $ Just 1) (Single (Just 3))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Just 4)
              `shouldBe` Guard
                (Just 1)
                True
                (And (SSBool "b") (SSBool "a"))
                (Single $ Just 1)
                (Guard (Just 3) True (SSBool "b") (Single $ Just 3) (Single $ Just 4))
          it "guardWithStrategy on Single/Guard for degenerated case with idxt > idxf" $ do
            let x =
                  guardWithStrategy
                    mergeStrategy
                    (SSBool "a")
                    (Single (Right (1 :: Integer)))
                    (Single (Right (2 :: Integer)))
            guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Left (1 :: Integer))
              `shouldBe` Guard
                (Left 1)
                True
                (Not $ SSBool "b")
                (Single $ Left 1)
                (Guard (Right 1) True (SSBool "a") (Single $ Right 1) (Single (Right 2)))
        it "guardWithStrategy on Single/Guard for idxtt < idxf" $ do
          let x =
                guardWithStrategy
                  mergeStrategy
                  (SSBool "a")
                  (Single $ Left (1 :: Integer))
                  (Single $ Right (3 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Right 0)
            `shouldBe` Guard
              (Left 1)
              True
              (And (SSBool "b") (SSBool "a"))
              (Single $ Left 1)
              (Guard (Right 0) True (Not $ SSBool "b") (Single $ Right 0) (Single $ Right 3))
        it "guardWithStrategy on Single/Guard for idxtt == idxf" $ do
          let x =
                guardWithStrategy
                  mergeStrategy
                  (SSBool "a")
                  (Single $ Left (1 :: Integer))
                  (Single $ Right (3 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "b") x (Single $ Left 0)
            `shouldBe` Guard
              (Left 0)
              True
              (Or (Not $ SSBool "b") (SSBool "a"))
              (Guard (Left 0) True (Not $ SSBool "b") (Single $ Left 0) (Single $ Left 1))
              (Single $ Right 3)
        it "guardWithStrategy on Single/Guard for idxtt > idxf" $ do
          let x =
                guardWithStrategy
                  mergeStrategy
                  (SSBool "a")
                  (Single (1 :: Integer))
                  (Single (3 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "b") x (Single 0)
            `shouldBe` Guard 0 True (Not $ SSBool "b") (Single 0) (Guard 1 True (SSBool "a") (Single 1) (Single 3))
      describe "guardWithStrategy on Guard/Guard" $ do
        it "guardWithStrategy on Guard/Guard degenerate to Single/Guard when idxtt == idxtf" $ do
          let x = guardWithStrategy mergeStrategy (SSBool "a") (Single $ Left (1 :: Integer)) (Single $ Left (2 :: Integer))
          let y = guardWithStrategy mergeStrategy (SSBool "b") (Single $ Left (1 :: Integer)) (Single $ Right (2 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "c") x y
            `shouldBe` Guard
              (Left 1)
              True
              (Or (SSBool "c") (SSBool "b"))
              (Guard (Left 1) True (Or (Not (SSBool "c")) (SSBool "a")) (Single $ Left 1) (Single $ Left 2))
              (Single $ Right 2)
        it "guardWithStrategy on Guard/Guard degenerate to Single/Guard when idxff == idxft" $ do
          let x = guardWithStrategy mergeStrategy (SSBool "a") (Single $ Left (1 :: Integer)) (Single $ Left (2 :: Integer))
          let y = guardWithStrategy mergeStrategy (SSBool "b") (Single $ Left (1 :: Integer)) (Single $ Right (2 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "c") y x
            `shouldBe` Guard
              (Left 1)
              True
              (Or (Not $ SSBool "c") (SSBool "b"))
              (Guard (Left 1) True (Or (SSBool "c") (SSBool "a")) (Single $ Left 1) (Single $ Left 2))
              (Single $ Right 2)
        it "guardWithStrategy on Guard/Guard non-degenerated case when idxtt < idxft" $ do
          let x = guardWithStrategy mergeStrategy (SSBool "a") (Single $ TS1 (1 :: Integer)) (Single $ TS2 (2 :: Integer))
          let y = guardWithStrategy mergeStrategy (SSBool "b") (Single $ TS2 (1 :: Integer)) (Single $ TS3 (2 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "c") x y
            `shouldBe` Guard
              (TS1 1)
              True
              (And (SSBool "c") (SSBool "a"))
              (Single $ TS1 1)
              ( Guard
                  (TS2 1)
                  True
                  (Or (SSBool "c") (SSBool "b"))
                  (Guard (TS2 1) True (Not $ SSBool "c") (Single $ TS2 1) (Single $ TS2 2))
                  (Single $ TS3 2)
              )
        it "guardWithStrategy on Guard/Guard non-degenerated case when idxtt == idxft" $ do
          let x = guardWithStrategy mergeStrategy (SSBool "a") (Single $ TS1 (1 :: Integer)) (Single $ TS2 (2 :: Integer))
          let y = guardWithStrategy mergeStrategy (SSBool "b") (Single $ TS1 (2 :: Integer)) (Single $ TS3 (2 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "c") x y
            `shouldBe` Guard
              (TS1 1)
              True
              (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
              (Guard (TS1 1) True (SSBool "c") (Single $ TS1 1) (Single $ TS1 2))
              (Guard (TS2 2) True (SSBool "c") (Single $ TS2 2) (Single $ TS3 2))
        it "guardWithStrategy on Guard/Guard non-degenerated case when idxtt > idxft" $ do
          let x = guardWithStrategy mergeStrategy (SSBool "a") (Single $ TS2 (1 :: Integer)) (Single $ TS3 (2 :: Integer))
          let y = guardWithStrategy mergeStrategy (SSBool "b") (Single $ TS1 (1 :: Integer)) (Single $ TS2 (2 :: Integer))
          guardWithStrategy mergeStrategy (SSBool "c") x y
            `shouldBe` Guard
              (TS1 1)
              True
              (And (Not $ SSBool "c") (SSBool "b"))
              (Single $ TS1 1)
              ( Guard
                  (TS2 1)
                  True
                  (Or (Not $ SSBool "c") (SSBool "a"))
                  (Guard (TS2 1) True (SSBool "c") (Single $ TS2 1) (Single $ TS2 2))
                  (Single $ TS3 2)
              )
    it "guardWithStrategy should tolerate non-merged Guards" $ do
      let x = Guard (Right 2) False (SSBool "a") (Single $ Right (2 :: Integer)) (Single $ Left (2 :: Integer))
      let y = Guard (Right 3) False (SSBool "b") (Single $ Right 3) (Single $ Left 1)
      guardWithStrategy mergeStrategy (SSBool "c") x y
        `shouldBe` Guard
          (Left 1)
          True
          (ITE (SSBool "c") (Not $ SSBool "a") (Not $ SSBool "b"))
          (Guard (Left 1) True (Not $ SSBool "c") (Single $ Left 1) (Single $ Left 2))
          (Guard (Right 2) True (SSBool "c") (Single $ Right 2) (Single $ Right 3))
  describe "fullReconstruct" $ do
    it "fullReconstruct should work" $ do
      let x = Guard (Right 2) False (SSBool "a") (Single $ Right (2 :: Integer)) (Single $ Left (2 :: Integer))
      let y = Guard (Right 3) False (SSBool "b") (Single $ Right 3) (Single $ Left 1)
      let z = Guard (Right 2) False (SSBool "c") x y
      fullReconstruct mergeStrategy z
        `shouldBe` Guard
          (Left 1)
          True
          (ITE (SSBool "c") (Not $ SSBool "a") (Not $ SSBool "b"))
          (Guard (Left 1) True (Not $ SSBool "c") (Single $ Left 1) (Single $ Left 2))
          (Guard (Right 2) True (SSBool "c") (Single $ Right 2) (Single $ Right 3))
