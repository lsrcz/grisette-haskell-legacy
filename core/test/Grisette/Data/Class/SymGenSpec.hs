module Grisette.Data.Class.SymGenSpec where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.SymGen
import Test.Hspec
import Utils.SBool

spec :: Spec
spec = do
  describe "SymGen for common types" $ do
    describe "SymGen for SBool" $ do
      it "SymGen for SBool with ()" $ do
        (genSym @SBool () "a" :: UnionMBase SBool SBool)
          `shouldBe` mrgReturn (ISBool 0 "a")
        (genSymSimple @SBool () "a" :: SBool)
          `shouldBe` ISBool 0 "a"
      it "SymGen for SBool with SBool" $ do
        (genSym @SBool (CBool True) "a" :: UnionMBase SBool SBool)
          `shouldBe` mrgReturn (ISBool 0 "a")
        (genSymSimple @SBool (CBool True) "a" :: SBool)
          `shouldBe` ISBool 0 "a"
    describe "SymGen for Bool" $ do
      it "SymGen for Bool with ()" $ do
        (genSym @SBool () "a" :: UnionMBase SBool Bool)
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn False) (mrgReturn True)
      it "SymGen for Bool with Bool" $ do
        (genSym @SBool True "a" :: UnionMBase SBool Bool)
          `shouldBe` mrgReturn True
        (genSym @SBool False "a" :: UnionMBase SBool Bool)
          `shouldBe` mrgReturn False
        (genSymSimple @SBool True "a" :: Bool)
          `shouldBe` True
        (genSymSimple @SBool False "a" :: Bool)
          `shouldBe` False
    describe "SymGen for Integer" $ do
      it "SymGen for Integer with Integer" $ do
        (genSym @SBool (1 :: Integer) "a" :: UnionMBase SBool Integer)
          `shouldBe` mrgReturn 1
        (genSymSimple @SBool (1 :: Integer) "a" :: Integer)
          `shouldBe` 1
      it "SymGen for Integer with upper bound" $ do
        (genSym @SBool (NumGenUpperBound (2 :: Integer)) "a" :: UnionMBase SBool Integer)
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgIf (ISBool 1 "a") (mrgReturn 1) (mrgReturn 2))
      it "SymGen for Integer with bound" $ do
        (genSym @SBool (NumGenBound (-1 :: Integer) 1) "a" :: UnionMBase SBool Integer)
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn (-1)) (mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1))
    describe "SymGen for Char" $ do
      it "SymGen for Char with Char" $ do
        (genSym @SBool 'x' "a" :: UnionMBase SBool Char)
          `shouldBe` mrgReturn 'x'
        (genSymSimple @SBool 'x' "a" :: Char) `shouldBe` 'x'
      it "SymGen for Integer with upper bound" $ do
        (genSym @SBool (NumGenUpperBound @Char (toEnum 3)) "a" :: UnionMBase SBool Char)
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn $ toEnum 0) (mrgIf (ISBool 1 "a") (mrgReturn $ toEnum 1) (mrgReturn $ toEnum 2))
      it "SymGen for Integer with bound" $ do
        (genSym @SBool (NumGenBound 'a' 'd') "a" :: UnionMBase SBool Char)
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn 'a') (mrgIf (ISBool 1 "a") (mrgReturn 'b') (mrgReturn 'c'))
    describe "SymGen for Maybe" $ do
      it "SymGen for Maybe with Maybe" $ do
        (genSym (Just (SSBool "a")) "a" :: UnionMBase SBool (Maybe SBool)) `shouldBe` mrgReturn (Just (ISBool 0 "a"))
        (genSym (Nothing :: Maybe SBool) "a" :: UnionMBase SBool (Maybe SBool)) `shouldBe` mrgReturn Nothing
        (genSymSimple @SBool (Just (SSBool "a")) "a" :: Maybe SBool) `shouldBe` Just (ISBool 0 "a")
        (genSymSimple @SBool (Nothing :: Maybe SBool) "a" :: Maybe SBool) `shouldBe` Nothing
      it "SymGen for Maybe with ()" $ do
        (genSym () "a" :: UnionMBase SBool (Maybe SBool))
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn Nothing) (mrgReturn (Just (ISBool 1 "a")))
    describe "SymGen for Either" $ do
      it "SymGen for Either with Either" $ do
        (genSym (Left (SSBool "a") :: Either SBool SBool) "a" :: UnionMBase SBool (Either SBool SBool))
          `shouldBe` mrgReturn (Left (ISBool 0 "a"))
        (genSym (Right (SSBool "a") :: Either SBool SBool) "a" :: UnionMBase SBool (Either SBool SBool))
          `shouldBe` mrgReturn (Right (ISBool 0 "a"))
        (genSymSimple @SBool (Left (SSBool "a") :: Either SBool SBool) "a" :: Either SBool SBool)
          `shouldBe` Left (ISBool 0 "a")
        (genSymSimple @SBool (Right (SSBool "a") :: Either SBool SBool) "a" :: Either SBool SBool)
          `shouldBe` Right (ISBool 0 "a")
      it "SymGen for Either with ()" $ do
        (genSym () "a" :: UnionMBase SBool (Either SBool SBool))
          `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn $ Left $ ISBool 1 "a") (mrgReturn $ Right $ ISBool 2 "a")
    describe "SymGen for List" $ do
      it "SymGen for List with max length" $ do
        (genSym (0 :: Integer) "a" :: UnionMBase SBool [SBool]) `shouldBe` mrgReturn []
        (genSym (3 :: Integer) "a" :: UnionMBase SBool [SBool])
          `shouldBe` mrgIf
            (ISBool 3 "a")
            (mrgReturn [])
            ( mrgIf
                (ISBool 4 "a")
                (mrgReturn [ISBool 2 "a"])
                ( mrgIf
                    (ISBool 5 "a")
                    (mrgReturn [ISBool 1 "a", ISBool 2 "a"])
                    (mrgReturn [ISBool 0 "a", ISBool 1 "a", ISBool 2 "a"])
                )
            )
      it "SymGen for List with min & max length" $ do
        (genSym (ListSpec 1 3 ()) "a" :: UnionMBase SBool [SBool])
          `shouldBe` mrgIf
            (ISBool 3 "a")
            (mrgReturn [ISBool 2 "a"])
            ( mrgIf
                (ISBool 4 "a")
                (mrgReturn [ISBool 1 "a", ISBool 2 "a"])
                (mrgReturn [ISBool 0 "a", ISBool 1 "a", ISBool 2 "a"])
            )
        (genSym (ListSpec 1 2 (ListSpec 1 2 ())) "a" :: UnionMBase SBool [UnionMBase SBool [SBool]])
          `shouldBe` mrgIf
            (ISBool 6 "a")
            ( mrgReturn
                [ mrgIf
                    (ISBool 5 "a")
                    (mrgReturn [ISBool 4 "a"])
                    (mrgReturn [ISBool 3 "a", ISBool 4 "a"])
                ]
            )
            ( mrgReturn
                [ mrgIf
                    (ISBool 2 "a")
                    (mrgReturn [ISBool 1 "a"])
                    (mrgReturn [ISBool 0 "a", ISBool 1 "a"]),
                  mrgIf
                    (ISBool 5 "a")
                    (mrgReturn [ISBool 4 "a"])
                    (mrgReturn [ISBool 3 "a", ISBool 4 "a"])
                ]
            )
      it "SymGen for List with exact length" $ do
        (genSym (SimpleListSpec 2 ()) "a" :: UnionMBase SBool [SBool])
          `shouldBe` mrgReturn [ISBool 0 "a", ISBool 1 "a"]
        (genSymSimple @SBool (SimpleListSpec 2 ()) "a" :: [SBool])
          `shouldBe` [ISBool 0 "a", ISBool 1 "a"]
        (genSym (SimpleListSpec 2 (SimpleListSpec 2 ())) "a" :: UnionMBase SBool [[SBool]])
          `shouldBe` mrgReturn [[ISBool 0 "a", ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]]
        (genSymSimple @SBool (SimpleListSpec 2 (SimpleListSpec 2 ())) "a" :: [[SBool]])
          `shouldBe` [[ISBool 0 "a", ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]]
      it "SymGen for List with same shape" $ do
        (genSym [[CBool True], [SSBool "a", SSBool "b"]] "a" :: UnionMBase SBool [[SBool]])
          `shouldBe` mrgReturn [[ISBool 0 "a"], [ISBool 1 "a", ISBool 2 "a"]]
        (genSymSimple @SBool [[CBool True], [SSBool "a", SSBool "b"]] "a" :: [[SBool]])
          `shouldBe` [[ISBool 0 "a"], [ISBool 1 "a", ISBool 2 "a"]]
    describe "SymGen for ()" $ do
      it "SymGen for () with ()" $ do
        (genSym () "a" :: UnionMBase SBool ()) `shouldBe` mrgReturn ()
        (genSymSimple @SBool () "a" :: ()) `shouldBe` ()
    describe "SymGen for (,)" $ do
      it "SymGen for (,) with some spec" $ do
        (genSym (NumGenUpperBound @Integer 1, NumGenUpperBound @Integer 1) "a" :: UnionMBase SBool (Integer, Integer))
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2)
        (genSymSimple @SBool ((), [[SSBool "b"], [SSBool "b", SSBool "c"]]) "a" :: (SBool, [[SBool]]))
          `shouldBe` (ISBool 0 "a", [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]])
      it "SymGen for (,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool)) `shouldBe` mrgReturn (ISBool 0 "a", ISBool 1 "a")
        (genSymSimple @SBool () "a" :: (SBool, SBool)) `shouldBe` (ISBool 0 "a", ISBool 1 "a")
    describe "SymGen for (,,)" $ do
      it "SymGen for (,,) with some spec" $ do
        ( genSym
            ( NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1
            )
            "a" ::
            UnionMBase SBool (Integer, Integer, Integer)
          )
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            x3 <- mrgIf (ISBool 2 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2, x3)
        (genSymSimple @SBool ((), [[SSBool "b"], [SSBool "b", SSBool "c"]], ()) "a" :: (SBool, [[SBool]], SBool))
          `shouldBe` (ISBool 0 "a", [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]], ISBool 4 "a")
      it "SymGen for (,,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool, SBool))
          `shouldBe` mrgReturn (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a")
        (genSymSimple @SBool () "a" :: (SBool, SBool, SBool)) `shouldBe` (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a")
    describe "SymGen for (,,,)" $ do
      it "SymGen for (,,,) with some spec" $ do
        ( genSym
            ( NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1
            )
            "a" ::
            UnionMBase SBool (Integer, Integer, Integer, Integer)
          )
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            x3 <- mrgIf (ISBool 2 "a") (mrgReturn 0) (mrgReturn 1)
            x4 <- mrgIf (ISBool 3 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2, x3, x4)
        ( genSymSimple @SBool
            ((), [[SSBool "b"], [SSBool "b", SSBool "c"]], (), ())
            "a" ::
            (SBool, [[SBool]], SBool, SBool)
          )
          `shouldBe` (ISBool 0 "a", [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]], ISBool 4 "a", ISBool 5 "a")
      it "SymGen for (,,,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool, SBool, SBool))
          `shouldBe` mrgReturn (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a")
        (genSymSimple @SBool () "a" :: (SBool, SBool, SBool, SBool))
          `shouldBe` (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a")
    describe "SymGen for (,,,,)" $ do
      it "SymGen for (,,,,) with some spec" $ do
        ( genSym
            ( NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1
            )
            "a" ::
            UnionMBase SBool (Integer, Integer, Integer, Integer, Integer)
          )
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            x3 <- mrgIf (ISBool 2 "a") (mrgReturn 0) (mrgReturn 1)
            x4 <- mrgIf (ISBool 3 "a") (mrgReturn 0) (mrgReturn 1)
            x5 <- mrgIf (ISBool 4 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2, x3, x4, x5)
        ( genSymSimple @SBool
            ((), [[SSBool "b"], [SSBool "b", SSBool "c"]], (), (), ())
            "a" ::
            (SBool, [[SBool]], SBool, SBool, SBool)
          )
          `shouldBe` (ISBool 0 "a", [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]], ISBool 4 "a", ISBool 5 "a", ISBool 6 "a")
      it "SymGen for (,,,,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool, SBool, SBool, SBool))
          `shouldBe` mrgReturn (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a", ISBool 4 "a")
        (genSymSimple @SBool () "a" :: (SBool, SBool, SBool, SBool, SBool))
          `shouldBe` (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a", ISBool 4 "a")
    describe "SymGen for (,,,,,)" $ do
      it "SymGen for (,,,,,) with some spec" $ do
        ( genSym
            ( NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1
            )
            "a" ::
            UnionMBase SBool (Integer, Integer, Integer, Integer, Integer, Integer)
          )
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            x3 <- mrgIf (ISBool 2 "a") (mrgReturn 0) (mrgReturn 1)
            x4 <- mrgIf (ISBool 3 "a") (mrgReturn 0) (mrgReturn 1)
            x5 <- mrgIf (ISBool 4 "a") (mrgReturn 0) (mrgReturn 1)
            x6 <- mrgIf (ISBool 5 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2, x3, x4, x5, x6)
        ( genSymSimple @SBool
            ((), [[SSBool "b"], [SSBool "b", SSBool "c"]], (), (), (), ())
            "a" ::
            (SBool, [[SBool]], SBool, SBool, SBool, SBool)
          )
          `shouldBe` ( ISBool 0 "a",
                       [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]],
                       ISBool 4 "a",
                       ISBool 5 "a",
                       ISBool 6 "a",
                       ISBool 7 "a"
                     )
      it "SymGen for (,,,,,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool, SBool, SBool, SBool, SBool))
          `shouldBe` mrgReturn (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a", ISBool 4 "a", ISBool 5 "a")
        (genSymSimple @SBool () "a" :: (SBool, SBool, SBool, SBool, SBool, SBool))
          `shouldBe` (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a", ISBool 4 "a", ISBool 5 "a")
    describe "SymGen for (,,,,,,)" $ do
      it "SymGen for (,,,,,,) with some spec" $ do
        ( genSym
            ( NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1
            )
            "a" ::
            UnionMBase SBool (Integer, Integer, Integer, Integer, Integer, Integer, Integer)
          )
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            x3 <- mrgIf (ISBool 2 "a") (mrgReturn 0) (mrgReturn 1)
            x4 <- mrgIf (ISBool 3 "a") (mrgReturn 0) (mrgReturn 1)
            x5 <- mrgIf (ISBool 4 "a") (mrgReturn 0) (mrgReturn 1)
            x6 <- mrgIf (ISBool 5 "a") (mrgReturn 0) (mrgReturn 1)
            x7 <- mrgIf (ISBool 6 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2, x3, x4, x5, x6, x7)
        ( genSymSimple @SBool
            ((), [[SSBool "b"], [SSBool "b", SSBool "c"]], (), (), (), (), ())
            "a" ::
            (SBool, [[SBool]], SBool, SBool, SBool, SBool, SBool)
          )
          `shouldBe` ( ISBool 0 "a",
                       [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]],
                       ISBool 4 "a",
                       ISBool 5 "a",
                       ISBool 6 "a",
                       ISBool 7 "a",
                       ISBool 8 "a"
                     )
      it "SymGen for (,,,,,,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool, SBool, SBool, SBool, SBool, SBool))
          `shouldBe` mrgReturn
            ( ISBool 0 "a",
              ISBool 1 "a",
              ISBool 2 "a",
              ISBool 3 "a",
              ISBool 4 "a",
              ISBool 5 "a",
              ISBool 6 "a"
            )
        (genSymSimple @SBool () "a" :: (SBool, SBool, SBool, SBool, SBool, SBool, SBool))
          `shouldBe` (ISBool 0 "a", ISBool 1 "a", ISBool 2 "a", ISBool 3 "a", ISBool 4 "a", ISBool 5 "a", ISBool 6 "a")
    describe "SymGen for (,,,,,,,)" $ do
      it "SymGen for (,,,,,,,) with some spec" $ do
        ( genSym
            ( NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1,
              NumGenUpperBound @Integer 1
            )
            "a" ::
            UnionMBase SBool (Integer, Integer, Integer, Integer, Integer, Integer, Integer, Integer)
          )
          `shouldBe` do
            x1 <- mrgIf (ISBool 0 "a") (mrgReturn 0) (mrgReturn 1)
            x2 <- mrgIf (ISBool 1 "a") (mrgReturn 0) (mrgReturn 1)
            x3 <- mrgIf (ISBool 2 "a") (mrgReturn 0) (mrgReturn 1)
            x4 <- mrgIf (ISBool 3 "a") (mrgReturn 0) (mrgReturn 1)
            x5 <- mrgIf (ISBool 4 "a") (mrgReturn 0) (mrgReturn 1)
            x6 <- mrgIf (ISBool 5 "a") (mrgReturn 0) (mrgReturn 1)
            x7 <- mrgIf (ISBool 6 "a") (mrgReturn 0) (mrgReturn 1)
            x8 <- mrgIf (ISBool 7 "a") (mrgReturn 0) (mrgReturn 1)
            mrgReturn (x1, x2, x3, x4, x5, x6, x7, x8)
        ( genSymSimple @SBool
            ((), [[SSBool "b"], [SSBool "b", SSBool "c"]], (), (), (), (), (), ())
            "a" ::
            (SBool, [[SBool]], SBool, SBool, SBool, SBool, SBool, SBool)
          )
          `shouldBe` ( ISBool 0 "a",
                       [[ISBool 1 "a"], [ISBool 2 "a", ISBool 3 "a"]],
                       ISBool 4 "a",
                       ISBool 5 "a",
                       ISBool 6 "a",
                       ISBool 7 "a",
                       ISBool 8 "a",
                       ISBool 9 "a"
                     )
      it "SymGen for (,,,,,,,) with no spec" $ do
        (genSym () "a" :: UnionMBase SBool (SBool, SBool, SBool, SBool, SBool, SBool, SBool, SBool))
          `shouldBe` mrgReturn
            ( ISBool 0 "a",
              ISBool 1 "a",
              ISBool 2 "a",
              ISBool 3 "a",
              ISBool 4 "a",
              ISBool 5 "a",
              ISBool 6 "a",
              ISBool 7 "a"
            )
        (genSymSimple @SBool () "a" :: (SBool, SBool, SBool, SBool, SBool, SBool, SBool, SBool))
          `shouldBe` ( ISBool 0 "a",
                       ISBool 1 "a",
                       ISBool 2 "a",
                       ISBool 3 "a",
                       ISBool 4 "a",
                       ISBool 5 "a",
                       ISBool 6 "a",
                       ISBool 7 "a"
                     )
    describe "SymGen for MaybeT" $ do
      it "SymGen for MaybeT with same shape" $ do
        (genSym (MaybeT Nothing :: MaybeT Maybe SBool) "a" :: UnionMBase SBool (MaybeT Maybe SBool))
          `shouldBe` mrgReturn (MaybeT Nothing)
        (genSymSimple @SBool (MaybeT Nothing :: MaybeT Maybe SBool) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT Nothing
        (genSym (MaybeT (Just Nothing) :: MaybeT Maybe SBool) "a" :: UnionMBase SBool (MaybeT Maybe SBool))
          `shouldBe` mrgReturn (MaybeT (Just Nothing))
        (genSymSimple @SBool (MaybeT (Just (Just $ SSBool "a")) :: MaybeT Maybe SBool) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT (Just (Just $ ISBool 0 "a"))
        (genSym (MaybeT (Just (Just $ SSBool "a")) :: MaybeT Maybe SBool) "a" :: UnionMBase SBool (MaybeT Maybe SBool))
          `shouldBe` mrgReturn (MaybeT (Just (Just $ ISBool 0 "a")))
        (genSymSimple @SBool (MaybeT (Just (Just $ SSBool "a")) :: MaybeT Maybe SBool) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT (Just (Just $ ISBool 0 "a"))
      it "SymGen for MaybeT with general spec" $ do
        (genSym () "a" :: UnionMBase SBool (MaybeT Maybe SBool))
          `shouldBe` mrgIf
            (ISBool 0 "a")
            (mrgReturn $ MaybeT Nothing)
            ( mrgIf
                (ISBool 1 "a")
                (mrgReturn $ MaybeT $ Just Nothing)
                (mrgReturn $ MaybeT $ Just $ Just $ ISBool 2 "a")
            )
        (genSymSimple @SBool (Nothing :: Maybe (Maybe SBool)) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT Nothing
        (genSymSimple @SBool (Just $ Nothing :: Maybe (Maybe SBool)) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT (Just Nothing)
        (genSymSimple @SBool (Just $ Just $ SSBool "a" :: Maybe (Maybe SBool)) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT (Just (Just $ ISBool 0 "a"))
        (genSymSimple @SBool (Just $ Just $ SSBool "a" :: Maybe (Maybe SBool)) "a" :: MaybeT Maybe SBool)
          `shouldBe` MaybeT (Just (Just $ ISBool 0 "a"))

    describe "SymGen for ExceptT" $ do
      it "SymGen for ExceptT with same shape" $ do
        (genSym (ExceptT Nothing :: ExceptT SBool Maybe SBool) "a" :: UnionMBase SBool (ExceptT SBool Maybe SBool))
          `shouldBe` mrgReturn (ExceptT Nothing)
        (genSymSimple @SBool (ExceptT Nothing :: ExceptT SBool Maybe SBool) "a" :: ExceptT SBool Maybe SBool)
          `shouldBe` ExceptT Nothing
        ( genSym (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool) "a" ::
            UnionMBase SBool (ExceptT SBool Maybe SBool)
          )
          `shouldBe` mrgReturn (ExceptT $ Just $ Left $ ISBool 0 "a")
        ( genSymSimple @SBool
            (ExceptT $ Just $ Left $ SSBool "a" :: ExceptT SBool Maybe SBool)
            "a" ::
            ExceptT SBool Maybe SBool
          )
          `shouldBe` ExceptT (Just $ Left $ ISBool 0 "a")
        ( genSym (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool) "a" ::
            UnionMBase SBool (ExceptT SBool Maybe SBool)
          )
          `shouldBe` mrgReturn (ExceptT $ Just $ Right $ ISBool 0 "a")
        ( genSymSimple @SBool
            (ExceptT $ Just $ Right $ SSBool "a" :: ExceptT SBool Maybe SBool)
            "a" ::
            ExceptT SBool Maybe SBool
          )
          `shouldBe` ExceptT (Just $ Right $ ISBool 0 "a")
    it "SymGen for ExceptT with general spec" $ do
      (genSym () "a" :: UnionMBase SBool (ExceptT SBool Maybe SBool))
        `shouldBe`
        mrgIf (ISBool 0 "a") (mrgReturn $ ExceptT Nothing)
          (mrgIf (ISBool 1 "a") (mrgReturn $ ExceptT $ Just $ Left $ ISBool 2 "a")
            (mrgReturn $ ExceptT $ Just $ Right $ ISBool 3 "a"))
      (genSymSimple @SBool (Nothing :: Maybe (Either SBool SBool)) "a" :: ExceptT SBool Maybe SBool)
        `shouldBe` ExceptT Nothing
      (genSymSimple @SBool (Just $ Left $ SSBool "a" :: Maybe (Either SBool SBool)) "a" :: ExceptT SBool Maybe SBool)
        `shouldBe` ExceptT (Just (Left $ ISBool 0 "a"))
      (genSymSimple @SBool (Just $ Right $ SSBool "a" :: Maybe (Either SBool SBool)) "a" :: ExceptT SBool Maybe SBool)
        `shouldBe` ExceptT (Just (Right $ ISBool 0 "a"))