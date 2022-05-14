{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Data.Class.MergeableSpec where

import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import qualified Data.ByteString.Char8 as C
import Data.Functor.Sum
import qualified Data.Vector as V
import qualified Data.Vector.Generic.Sized as VSized
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.UnionOp
import Test.Hspec
import Test.Hspec.QuickCheck
import Utils.SBool
import Data.Int
import Data.Word

testMergeableSimpleEquivClass ::
  (HasCallStack, Mergeable SBool x, Show x, Eq x) => x -> [DynamicOrderedIdx] -> [(SBool, x, x, x)] -> Expectation
testMergeableSimpleEquivClass x idxs cases = do
  let (idxsT, s) = resolveStrategy @SBool x
  case s of
    SimpleStrategy m -> do
      idxsT `shouldBe` idxs
      go cases
      where
        go [] = return ()
        go ((c, t, f, r) : xs) = do
          fst (resolveStrategy @SBool t) `shouldBe` idxs
          fst (resolveStrategy @SBool f) `shouldBe` idxs
          fst (resolveStrategy @SBool r) `shouldBe` idxs
          m c t f `shouldBe` r
          go xs
    _ -> expectationFailure $ "Bad strategy type for " ++ show x

testMergeableSimpleEquivClass' ::
  (HasCallStack, Mergeable SBool x, Show y, Eq y) => (x -> y) -> x -> [DynamicOrderedIdx] -> [(SBool, x, x, x)] -> Expectation
testMergeableSimpleEquivClass' vis x idxs cases = do
  let (idxsT, s) = resolveStrategy @SBool x
  case s of
    SimpleStrategy m -> do
      idxsT `shouldBe` idxs
      go cases
      where
        go [] = return ()
        go ((c, t, f, r) : xs) = do
          fst (resolveStrategy @SBool t) `shouldBe` idxs
          fst (resolveStrategy @SBool f) `shouldBe` idxs
          fst (resolveStrategy @SBool r) `shouldBe` idxs
          vis (m c t f) `shouldBe` vis r
          go xs
    _ -> expectationFailure $ "Bad strategy type for " ++ show (vis x)

spec :: Spec
spec = do
  describe "Mergeable for common types" $ do
    describe "Mergeable for SBool" $ do
      it "Mergeable for SBool should work" $ do
        let SimpleStrategy f = mergeStrategy :: MergeStrategy SBool SBool
        f (CBool True) (SSBool "a") (SSBool "b") `shouldBe` SSBool "a"
        f (CBool False) (SSBool "a") (SSBool "b") `shouldBe` SSBool "b"
        f (SSBool "a") (SSBool "b") (SSBool "c") `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "c")
    describe "Mergeable for Bool" $ do
      prop "Mergeable for Bool should work" $ \(x :: Bool) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Integer" $ do
      prop "Mergeable for Integer should work" $ \(x :: Integer) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Char" $ do
      prop "Mergeable for Char should work" $ \(x :: Char) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Int" $ do
      prop "Mergeable for Int should work" $ \(x :: Int) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Int8" $ do
      prop "Mergeable for Int8 should work" $ \(x :: Int8) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Int16" $ do
      prop "Mergeable for Int16 should work" $ \(x :: Int16) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Int32" $ do
      prop "Mergeable for Int32 should work" $ \(x :: Int32) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Int64" $ do
      prop "Mergeable for Int64 should work" $ \(x :: Int64) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Word" $ do
      prop "Mergeable for Word should work" $ \(x :: Word) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Word8" $ do
      prop "Mergeable for Word8 should work" $ \(x :: Word8) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Word16" $ do
      prop "Mergeable for Word16 should work" $ \(x :: Word16) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Word32" $ do
      prop "Mergeable for Word32 should work" $ \(x :: Word32) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for Word64" $ do
      prop "Mergeable for Word64 should work" $ \(x :: Word64) ->
        testMergeableSimpleEquivClass x [DynamicOrderedIdx x] [(SSBool "a", x, x, x)]
    describe "Mergeable for ()" $ do
      prop "Mergeable for () should work" $ \(x :: ()) ->
        testMergeableSimpleEquivClass x [] [(SSBool "a", x, x, x)]
    describe "Mergeable for ByteString" $ do
      prop "Mergeable for ByteString should work" $ \(x :: String) ->
        let b = C.pack x
         in testMergeableSimpleEquivClass b [DynamicOrderedIdx b] [(SSBool "a", b, b, b)]
    describe "Mergeable for Either" $ do
      prop "Mergeable for Either Integer Integer should work" $ \(x :: Integer) -> do
        testMergeableSimpleEquivClass
          (Left x :: Either Integer Integer)
          [DynamicOrderedIdx False, DynamicOrderedIdx x]
          [(SSBool "a", Left x, Left x, Left x)]
        testMergeableSimpleEquivClass
          (Right x :: Either Integer Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", Right x, Right x, Right x)]
      it "Mergeable for Either SBool SBool should work" $ do
        let (idxsL, SimpleStrategy fL) = resolveStrategy @SBool (Left (SSBool "a") :: Either SBool SBool)
        idxsL `shouldBe` [DynamicOrderedIdx False]
        fL (SSBool "a") (Left $ SSBool "b") (Left $ SSBool "c")
          `shouldBe` Left (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
        let (idxsR, SimpleStrategy fR) = resolveStrategy @SBool (Right (SSBool "a") :: Either SBool SBool)
        idxsR `shouldBe` [DynamicOrderedIdx True]
        fR (SSBool "a") (Right $ SSBool "b") (Right $ SSBool "c")
          `shouldBe` Right (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    describe "Mergeable for Maybe" $ do
      prop "Mergeable for Maybe Integer should work" $ \(x :: Integer) -> do
        testMergeableSimpleEquivClass
          (Nothing :: Maybe Integer)
          [DynamicOrderedIdx False]
          [(SSBool "a", Nothing, Nothing, Nothing)]
        testMergeableSimpleEquivClass
          (Just x :: Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", Just x, Just x, Just x)]
      it "Mergeable for Maybe SBool should work" $ do
        let (idxsJ, SimpleStrategy fJ) = resolveStrategy @SBool (Just (SSBool "a") :: Maybe SBool)
        idxsJ `shouldBe` [DynamicOrderedIdx True]
        fJ (SSBool "a") (Just $ SSBool "b") (Just $ SSBool "c")
          `shouldBe` Just (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    describe "Mergeable for List" $ do
      it "BuildStrategyList should work" $ do
        case buildStrategyList @SBool @Integer [1, 2, 3] of
          StrategyList idxs _ -> do
            idxs
              `shouldBe` [ [DynamicOrderedIdx (1 :: Integer)],
                           [DynamicOrderedIdx (2 :: Integer)],
                           [DynamicOrderedIdx (3 :: Integer)]
                         ]
      prop "Mergeable for List for ordered type should work" $ \(x :: [Integer]) -> do
        testMergeableSimpleEquivClass
          x
          [DynamicOrderedIdx (length x), DynamicOrderedIdx $ buildStrategyList @SBool x]
          [(SSBool "a", x, x, x)]
      prop "Mergeable for nested List for ordered type should work" $ \(x :: [[Integer]]) -> do
        testMergeableSimpleEquivClass
          x
          [DynamicOrderedIdx (length x), DynamicOrderedIdx $ buildStrategyList @SBool x]
          [(SSBool "a", x, x, x)]
      it "Mergeable for List for simple type should work" $ do
        testMergeableSimpleEquivClass
          ([] :: [SBool])
          [DynamicOrderedIdx (0 :: Int)]
          [(SSBool "a", [], [], [])]
        testMergeableSimpleEquivClass
          [SSBool "a", SSBool "b"]
          [DynamicOrderedIdx (2 :: Int)]
          [ ( SSBool "a",
              [SSBool "b", SSBool "c"],
              [SSBool "d", SSBool "e"],
              [ITE (SSBool "a") (SSBool "b") (SSBool "d"), ITE (SSBool "a") (SSBool "c") (SSBool "e")]
            )
          ]
    describe "Mergeable for (,)" $ do
      it "Mergeable for (,) should work" $ do
        testMergeableSimpleEquivClass
          ([1 :: Integer], [SSBool "b", SSBool "c"])
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int)
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"]),
              ([1], [SSBool "f", SSBool "g"]),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ]
              )
            )
          ]
    describe "Mergeable for (,,)" $ do
      it "Mergeable for (,,) should work" $ do
        testMergeableSimpleEquivClass
          ([1 :: Integer], [SSBool "b", SSBool "c"], SSBool "d")
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int)
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"], SSBool "e"),
              ([1], [SSBool "f", SSBool "g"], SSBool "h"),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ],
                ITE (SSBool "a") (SSBool "e") (SSBool "h")
              )
            )
          ]
    describe "Mergeable for (,,,)" $ do
      it "Mergeable for (,,,) should work" $ do
        testMergeableSimpleEquivClass
          ([1 :: Integer], [SSBool "b", SSBool "c"], SSBool "d", [SSBool "f"])
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx (1 :: Int)
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"], SSBool "e", [SSBool "i"]),
              ([1], [SSBool "f", SSBool "g"], SSBool "h", [SSBool "j"]),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ],
                ITE (SSBool "a") (SSBool "e") (SSBool "h"),
                [ITE (SSBool "a") (SSBool "i") (SSBool "j")]
              )
            )
          ]
    describe "Mergeable for (,,,,)" $ do
      it "Mergeable for (,,,,) should work" $ do
        testMergeableSimpleEquivClass
          ([1 :: Integer], [SSBool "b", SSBool "c"], SSBool "d", [SSBool "f"], [2 :: Integer, 3])
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [2 :: Integer, 3]
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"], SSBool "e", [SSBool "i"], [2, 3]),
              ([1], [SSBool "f", SSBool "g"], SSBool "h", [SSBool "j"], [2, 3]),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ],
                ITE (SSBool "a") (SSBool "e") (SSBool "h"),
                [ITE (SSBool "a") (SSBool "i") (SSBool "j")],
                [2, 3]
              )
            )
          ]
    describe "Mergeable for (,,,,,)" $ do
      it "Mergeable for (,,,,,) should work" $ do
        testMergeableSimpleEquivClass
          ([1 :: Integer], [SSBool "b", SSBool "c"], SSBool "d", [SSBool "f"], [2 :: Integer, 3], 2 :: Integer)
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [2 :: Integer, 3],
            DynamicOrderedIdx (2 :: Integer)
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"], SSBool "e", [SSBool "i"], [2, 3], 2),
              ([1], [SSBool "f", SSBool "g"], SSBool "h", [SSBool "j"], [2, 3], 2),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ],
                ITE (SSBool "a") (SSBool "e") (SSBool "h"),
                [ITE (SSBool "a") (SSBool "i") (SSBool "j")],
                [2, 3],
                2
              )
            )
          ]
    describe "Mergeable for (,,,,,,)" $ do
      it "Mergeable for (,,,,,,) should work" $ do
        testMergeableSimpleEquivClass
          ( [1 :: Integer],
            [SSBool "b", SSBool "c"],
            SSBool "d",
            [SSBool "f"],
            [2 :: Integer, 3],
            2 :: Integer,
            Just (SSBool "a")
          )
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [2 :: Integer, 3],
            DynamicOrderedIdx (2 :: Integer),
            DynamicOrderedIdx True
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"], SSBool "e", [SSBool "i"], [2, 3], 2, Just (SSBool "k")),
              ([1], [SSBool "f", SSBool "g"], SSBool "h", [SSBool "j"], [2, 3], 2, Just (SSBool "l")),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ],
                ITE (SSBool "a") (SSBool "e") (SSBool "h"),
                [ITE (SSBool "a") (SSBool "i") (SSBool "j")],
                [2, 3],
                2,
                Just $ ITE (SSBool "a") (SSBool "k") (SSBool "l")
              )
            )
          ]
    describe "Mergeable for (,,,,,,,)" $ do
      it "Mergeable for (,,,,,,,) should work" $ do
        testMergeableSimpleEquivClass
          ( [1 :: Integer],
            [SSBool "b", SSBool "c"],
            SSBool "d",
            [SSBool "f"],
            [2 :: Integer, 3],
            2 :: Integer,
            Just (SSBool "a"),
            Left 1 :: Either Integer Integer
          )
          [ DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [1 :: Integer],
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx (1 :: Int),
            DynamicOrderedIdx (2 :: Int),
            DynamicOrderedIdx $ buildStrategyList @SBool [2 :: Integer, 3],
            DynamicOrderedIdx (2 :: Integer),
            DynamicOrderedIdx True,
            DynamicOrderedIdx False,
            DynamicOrderedIdx (1 :: Integer)
          ]
          [ ( SSBool "a",
              ([1], [SSBool "c", SSBool "d"], SSBool "e", [SSBool "i"], [2, 3], 2, Just (SSBool "k"), Left 1),
              ([1], [SSBool "f", SSBool "g"], SSBool "h", [SSBool "j"], [2, 3], 2, Just (SSBool "l"), Left 1),
              ( [1],
                [ ITE (SSBool "a") (SSBool "c") (SSBool "f"),
                  ITE (SSBool "a") (SSBool "d") (SSBool "g")
                ],
                ITE (SSBool "a") (SSBool "e") (SSBool "h"),
                [ITE (SSBool "a") (SSBool "i") (SSBool "j")],
                [2, 3],
                2,
                Just $ ITE (SSBool "a") (SSBool "k") (SSBool "l"),
                Left 1
              )
            )
          ]
    describe "Mergeable for function" $ do
      let f1 :: Maybe SBool -> SBool = \case Just x -> x; Nothing -> (CBool True)
      let f2 :: Maybe SBool -> SBool = \case Just x -> (nots x); Nothing -> (CBool False)
      it "Mergeable for function with simply mergeable result" $ do
        case mergeStrategy :: MergeStrategy SBool (Maybe SBool -> SBool) of
          SimpleStrategy f -> do
            let r = f (SSBool "a") f1 f2
            r (Just (SSBool "x")) `shouldBe` ITE (SSBool "a") (SSBool "x") (Not (SSBool "x"))
            r Nothing `shouldBe` ITE (SSBool "a") (CBool True) (CBool False)
          _ -> expectationFailure "Bad mergeable strategy type"
      it "Mergeable for function with other mergeable result" $ do
        case mergeStrategy :: MergeStrategy SBool (Maybe SBool -> Integer) of
          NoStrategy -> return ()
          _ -> expectationFailure "Bad mergeable strategy type"
    describe "Mergeable for MaybeT" $ do
      prop "Mergeable for MaybeT Maybe Integer should work" $ \(x :: Integer) -> do
        testMergeableSimpleEquivClass
          (MaybeT Nothing :: MaybeT Maybe Integer)
          [DynamicOrderedIdx False]
          [(SSBool "a", MaybeT Nothing, MaybeT Nothing, MaybeT Nothing)]
        testMergeableSimpleEquivClass
          (MaybeT $ Just Nothing :: MaybeT Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx False]
          [(SSBool "a", MaybeT $ Just Nothing, MaybeT $ Just Nothing, MaybeT $ Just Nothing)]
        testMergeableSimpleEquivClass
          (MaybeT $ Just $ Just x :: MaybeT Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", MaybeT $ Just $ Just x, MaybeT $ Just $ Just x, MaybeT $ Just $ Just x)]
      it "Mergeable for MaybeT Maybe SBool should work" $ do
        let (idxsJ, SimpleStrategy fJ) =
              resolveStrategy @SBool
                (MaybeT (Just (Just (SSBool "a"))) :: MaybeT Maybe SBool)
        idxsJ `shouldBe` [DynamicOrderedIdx True, DynamicOrderedIdx True]
        fJ (SSBool "a") (MaybeT $ Just $ Just $ SSBool "b") (MaybeT $ Just $ Just $ SSBool "c")
          `shouldBe` MaybeT (Just (Just (ITE (SSBool "a") (SSBool "b") (SSBool "c"))))
    describe "Mergeable for ExceptT" $ do
      prop "Mergeable for ExceptT Integer Maybe Integer should work" $ \(x :: Integer) -> do
        testMergeableSimpleEquivClass
          (ExceptT Nothing :: ExceptT Integer Maybe Integer)
          [DynamicOrderedIdx False]
          [(SSBool "a", ExceptT Nothing, ExceptT Nothing, ExceptT Nothing)]
        testMergeableSimpleEquivClass
          (ExceptT $ Just $ Left x :: ExceptT Integer Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx False, DynamicOrderedIdx x]
          [(SSBool "a", ExceptT $ Just $ Left x, ExceptT $ Just $ Left x, ExceptT $ Just $ Left x)]
        testMergeableSimpleEquivClass
          (ExceptT $ Just $ Right x :: ExceptT Integer Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", ExceptT $ Just $ Right x, ExceptT $ Just $ Right x, ExceptT $ Just $ Right x)]
      it "Mergeable for ExceptT SBool Maybe SBool should work" $ do
        let (idxsJL, SimpleStrategy fJL) =
              resolveStrategy @SBool
                (ExceptT (Just (Left (SSBool "a"))) :: ExceptT SBool Maybe SBool)
        idxsJL `shouldBe` [DynamicOrderedIdx True, DynamicOrderedIdx False]
        fJL (SSBool "a") (ExceptT $ Just $ Left $ SSBool "b") (ExceptT $ Just $ Left $ SSBool "c")
          `shouldBe` ExceptT (Just (Left (ITE (SSBool "a") (SSBool "b") (SSBool "c"))))
        let (idxsJR, SimpleStrategy fJR) =
              resolveStrategy @SBool
                (ExceptT (Just (Right (SSBool "a"))) :: ExceptT SBool Maybe SBool)
        idxsJR `shouldBe` [DynamicOrderedIdx True, DynamicOrderedIdx True]
        fJR (SSBool "a") (ExceptT $ Just $ Right $ SSBool "b") (ExceptT $ Just $ Right $ SSBool "c")
          `shouldBe` ExceptT (Just (Right (ITE (SSBool "a") (SSBool "b") (SSBool "c"))))
    describe "Mergeable for StateT" $ do
      it "Mergeable for lazy StateT should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (StateLazy.StateT Integer (UnionMBase SBool) SBool)
        let st1 :: StateLazy.StateT Integer (UnionMBase SBool) SBool =
              StateLazy.StateT $ \(x :: Integer) -> mrgReturn (SSBool "a", x + 2)
        let st2 :: StateLazy.StateT Integer (UnionMBase SBool) SBool =
              StateLazy.StateT $ \(x :: Integer) -> mrgReturn (SSBool "b", x * 2)
        let st3 = s (SSBool "c") st1 st2
        StateLazy.runStateT st3 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st3 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
      it "Mergeable for strict StateT should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (StateStrict.StateT Integer (UnionMBase SBool) SBool)
        let st1 :: StateStrict.StateT Integer (UnionMBase SBool) SBool =
              StateStrict.StateT $ \(x :: Integer) -> mrgReturn (SSBool "a", x + 2)
        let st2 :: StateStrict.StateT Integer (UnionMBase SBool) SBool =
              StateStrict.StateT $ \(x :: Integer) -> mrgReturn (SSBool "b", x * 2)
        let st3 = s (SSBool "c") st1 st2
        StateStrict.runStateT st3 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st3 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
    describe "Mergeable for WriterT" $ do
      it "Mergeable for lazy WriterT should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (WriterLazy.WriterT Integer (UnionMBase SBool) SBool)
        let w1 :: WriterLazy.WriterT Integer (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgReturn (SSBool "a", 1)
        let w2 :: WriterLazy.WriterT Integer (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgReturn (SSBool "b", 2)
        let w3 :: WriterLazy.WriterT Integer (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgReturn (SSBool "c", 1)
        let w4 = s (SSBool "d") w1 w2
        let w5 = s (SSBool "d") w1 w3
        WriterLazy.runWriterT w4 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterLazy.runWriterT w5 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
      it "Mergeable for strict WriterT should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (WriterStrict.WriterT Integer (UnionMBase SBool) SBool)
        let w1 :: WriterStrict.WriterT Integer (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgReturn (SSBool "a", 1)
        let w2 :: WriterStrict.WriterT Integer (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgReturn (SSBool "b", 2)
        let w3 :: WriterStrict.WriterT Integer (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgReturn (SSBool "c", 1)
        let w4 = s (SSBool "d") w1 w2
        let w5 = s (SSBool "d") w1 w3
        WriterStrict.runWriterT w4 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterStrict.runWriterT w5 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
    describe "Mergeable for ReaderT" $ do
      it "Mergeable for ReaderT should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (ReaderT Integer (UnionMBase SBool) Integer)
        let r1 :: ReaderT Integer (UnionMBase SBool) Integer =
              ReaderT $ \(x :: Integer) -> mrgReturn $ x + 2
        let r2 :: ReaderT Integer (UnionMBase SBool) Integer =
              ReaderT $ \(x :: Integer) -> mrgReturn $ x * 2
        let r3 = s (SSBool "c") r1 r2
        runReaderT r3 2 `shouldBe` mrgReturn 4
        runReaderT r3 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn 5) (mrgReturn 6)
    describe "Mergeable for Identity" $ do
      prop "Mergeable for Identity Integer should work" $ \x -> do
        testMergeableSimpleEquivClass
          (Identity x :: Identity Integer)
          [DynamicOrderedIdx x]
          [(SSBool "a", Identity x, Identity x, Identity x)]
      it "Mergeable for Identity SBool should work" $ do
        testMergeableSimpleEquivClass
          (Identity $ SSBool "a")
          []
          [ ( SSBool "a",
              Identity $ SSBool "b",
              Identity $ SSBool "c",
              Identity $ ITE (SSBool "a") (SSBool "b") (SSBool "c")
            )
          ]
    describe "Mergeable for IdentityT" $ do
      prop "Mergeable for IdentityT Maybe Integer should work" $ \x -> do
        testMergeableSimpleEquivClass
          (IdentityT Nothing :: IdentityT Maybe Integer)
          [DynamicOrderedIdx False]
          [(SSBool "a", IdentityT Nothing, IdentityT Nothing, IdentityT Nothing)]
        testMergeableSimpleEquivClass
          (IdentityT $ Just x :: IdentityT Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", IdentityT $ Just x, IdentityT $ Just x, IdentityT $ Just x)]
      it "Mergeable for IdentityT Maybe SBool should work" $ do
        testMergeableSimpleEquivClass
          (IdentityT Nothing :: IdentityT Maybe SBool)
          [DynamicOrderedIdx False]
          [(SSBool "a", IdentityT Nothing, IdentityT Nothing, IdentityT Nothing)]
        testMergeableSimpleEquivClass
          (IdentityT $ Just $ SSBool "a" :: IdentityT Maybe SBool)
          [DynamicOrderedIdx True]
          [ ( SSBool "a",
              IdentityT $ Just $ SSBool "b",
              IdentityT $ Just $ SSBool "c",
              IdentityT $ Just $ ITE (SSBool "a") (SSBool "b") (SSBool "c")
            )
          ]
    describe "Mergeable for Sum" $ do
      prop "Mergeable for Sum Maybe Maybe Integer should work" $ \x -> do
        testMergeableSimpleEquivClass
          (InL Nothing :: Sum Maybe Maybe Integer)
          [DynamicOrderedIdx False, DynamicOrderedIdx False]
          [(SSBool "a", InL Nothing, InL Nothing, InL Nothing)]
        testMergeableSimpleEquivClass
          (InL $ Just x :: Sum Maybe Maybe Integer)
          [DynamicOrderedIdx False, DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", InL $ Just x, InL $ Just x, InL $ Just x)]
        testMergeableSimpleEquivClass
          (InR Nothing :: Sum Maybe Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx False]
          [(SSBool "a", InR Nothing, InR Nothing, InR Nothing)]
        testMergeableSimpleEquivClass
          (InR $ Just x :: Sum Maybe Maybe Integer)
          [DynamicOrderedIdx True, DynamicOrderedIdx True, DynamicOrderedIdx x]
          [(SSBool "a", InR $ Just x, InR $ Just x, InR $ Just x)]
      it "Mergeable for Sum Maybe Maybe SBool should work" $ do
        testMergeableSimpleEquivClass
          (InL Nothing :: Sum Maybe Maybe SBool)
          [DynamicOrderedIdx False, DynamicOrderedIdx False]
          [(SSBool "a", InL Nothing, InL Nothing, InL Nothing)]
        testMergeableSimpleEquivClass
          (InL $ Just $ SSBool "a" :: Sum Maybe Maybe SBool)
          [DynamicOrderedIdx False, DynamicOrderedIdx True]
          [ ( SSBool "a",
              InL $ Just $ SSBool "b",
              InL $ Just $ SSBool "c",
              InL $ Just $ ITE (SSBool "a") (SSBool "b") (SSBool "c")
            )
          ]
        testMergeableSimpleEquivClass
          (InR Nothing :: Sum Maybe Maybe SBool)
          [DynamicOrderedIdx True, DynamicOrderedIdx False]
          [(SSBool "a", InR Nothing, InR Nothing, InR Nothing)]
        testMergeableSimpleEquivClass
          (InR $ Just $ SSBool "a" :: Sum Maybe Maybe SBool)
          [DynamicOrderedIdx True, DynamicOrderedIdx True]
          [ ( SSBool "a",
              InR $ Just $ SSBool "b",
              InR $ Just $ SSBool "c",
              InR $ Just $ ITE (SSBool "a") (SSBool "b") (SSBool "c")
            )
          ]
    describe "Mergeable for Coroutine" $ do
      prop "Mergeable for Yield Integer Integer should work" $ \(x :: Integer, y :: Integer) -> do
        testMergeableSimpleEquivClass'
          (\(Yield a b) -> (a, b))
          (Yield x y)
          [DynamicOrderedIdx x, DynamicOrderedIdx y]
          [(SSBool "a", Yield x y, Yield x y, Yield x y)]
      it "Mergeable for Yield SBool SBool should work" $ do
        testMergeableSimpleEquivClass'
          (\(Yield a b) -> (a, b))
          (Yield (SSBool "a") (SSBool "b"))
          []
          [ ( SSBool "a",
              Yield (SSBool "b") (SSBool "c"),
              Yield (SSBool "d") (SSBool "e"),
              Yield (ITE (SSBool "a") (SSBool "b") (SSBool "d")) (ITE (SSBool "a") (SSBool "c") (SSBool "e"))
            )
          ]
      it "Mergeable for Await SBool SBool should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (Await SBool SBool)
        let a1 = Await Not
        let a2 = Await (And (SSBool "a"))
        let Await a3 = s (SSBool "b") a1 a2
        a3 (SSBool "c") `shouldBe` ITE (SSBool "b") (Not (SSBool "c")) (And (SSBool "a") (SSBool "c"))
      it "Mergeable for Request SBool SBool SBool should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (Request SBool SBool SBool)
        let a1 = Request (SSBool "a") Not
        let a2 = Request (SSBool "b") (And (SSBool "c"))
        let Request v3 a3 = s (SSBool "d") a1 a2
        v3 `shouldBe` ITE (SSBool "d") (SSBool "a") (SSBool "b")
        a3 (SSBool "e") `shouldBe` ITE (SSBool "d") (Not (SSBool "e")) (And (SSBool "c") (SSBool "e"))
      it "Mergeable for Coroutine should work" $ do
        let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (Coroutine (Yield SBool) (UnionMBase SBool) SBool)
        let a1 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
              Coroutine (mrgReturn (Left (Yield (SSBool "a") (Coroutine (mrgReturn (Right $ SSBool "b"))))))
        let a2 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
              Coroutine (mrgReturn (Left (Yield (SSBool "c") (Coroutine (mrgReturn (Right $ SSBool "d"))))))
        let Coroutine r = s (SSBool "e") a1 a2
        case r of
          SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
            x `shouldBe` ITE (SSBool "e") (SSBool "a") (SSBool "c")
            y `shouldBe` ITE (SSBool "e") (SSBool "b") (SSBool "d")
          _ -> expectationFailure "Bad shape"
    describe "Mergeable for Ordering" $ do
      it "Mergeable for Ordering should work" $ do
        testMergeableSimpleEquivClass
          LT
          [DynamicOrderedIdx False]
          [(SSBool "a", LT, LT, LT)]
        testMergeableSimpleEquivClass
          EQ
          [DynamicOrderedIdx True, DynamicOrderedIdx False]
          [(SSBool "a", EQ, EQ, EQ)]
        testMergeableSimpleEquivClass
          GT
          [DynamicOrderedIdx True, DynamicOrderedIdx True]
          [(SSBool "a", GT, GT, GT)]
    describe "Mergeable for Sized Vector" $ do
      it "Mergeable for Sized Vector with simple mergeable contents" $ do
        testMergeableSimpleEquivClass
          (VSized.cons (SSBool "a") (VSized.cons (SSBool "b") VSized.empty) :: VSized.Vector V.Vector 2 SBool)
          []
          [ ( SSBool "a",
              VSized.cons (SSBool "b") (VSized.cons (SSBool "c") VSized.empty),
              VSized.cons (SSBool "d") (VSized.cons (SSBool "e") VSized.empty),
              VSized.cons
                (ITE (SSBool "a") (SSBool "b") (SSBool "d"))
                (VSized.cons (ITE (SSBool "a") (SSBool "c") (SSBool "e")) VSized.empty)
            )
          ]
      it "BuildStrategyList should work for Sized Vector" $ do
        case buildStrategyList @SBool @Integer
          (VSized.cons 1 (VSized.cons 2 (VSized.cons 3 VSized.empty)) :: VSized.Vector V.Vector 3 Integer) of
          StrategyList idxs _ -> do
            idxs
              `shouldBe` VSized.cons
                [DynamicOrderedIdx (1 :: Integer)]
                ( VSized.cons
                    [DynamicOrderedIdx (2 :: Integer)]
                    ( VSized.singleton
                        [DynamicOrderedIdx (3 :: Integer)]
                    )
                )
      prop "Mergeable for Sized Vector for ordered type should work" $ \(x, y, z) -> do
        let v = VSized.cons x (VSized.cons y (VSized.cons z VSized.empty)) :: VSized.Vector V.Vector 3 Integer
        testMergeableSimpleEquivClass
          v
          [DynamicOrderedIdx $ buildStrategyList @SBool v]
          [(SSBool "a", v, v, v)]
      it "Mergeable for Sized Vector for complex ordered type should work" $ do
        let v1 = VSized.cons Nothing (VSized.singleton Nothing) :: VSized.Vector V.Vector 2 (Maybe SBool)
        let v2 = VSized.cons (Just $ SSBool "a") (VSized.singleton Nothing) :: VSized.Vector V.Vector 2 (Maybe SBool)
        let v2' = VSized.cons (Just $ SSBool "b") (VSized.singleton Nothing) :: VSized.Vector V.Vector 2 (Maybe SBool)
        let v3 = VSized.cons Nothing (VSized.singleton (Just $ SSBool "a")) :: VSized.Vector V.Vector 2 (Maybe SBool)
        let v3' = VSized.cons Nothing (VSized.singleton (Just $ SSBool "b")) :: VSized.Vector V.Vector 2 (Maybe SBool)
        let v4 = VSized.cons (Just $ SSBool "a") (VSized.singleton (Just $ SSBool "b")) :: VSized.Vector V.Vector 2 (Maybe SBool)
        let v4' = VSized.cons (Just $ SSBool "c") (VSized.singleton (Just $ SSBool "d")) :: VSized.Vector V.Vector 2 (Maybe SBool)
        testMergeableSimpleEquivClass
          v1
          [DynamicOrderedIdx $ buildStrategyList @SBool v1]
          [(SSBool "a", v1, v1, v1)]
        testMergeableSimpleEquivClass
          v2
          [DynamicOrderedIdx $ buildStrategyList @SBool v2]
          [(SSBool "c", v2, v2', VSized.cons (Just $ ITE (SSBool "c") (SSBool "a") (SSBool "b")) (VSized.singleton Nothing))]
        testMergeableSimpleEquivClass
          v3
          [DynamicOrderedIdx $ buildStrategyList @SBool v3]
          [(SSBool "c", v3, v3', VSized.cons Nothing (VSized.singleton (Just $ ITE (SSBool "c") (SSBool "a") (SSBool "b"))))]
        testMergeableSimpleEquivClass
          v4
          [DynamicOrderedIdx $ buildStrategyList @SBool v4]
          [ ( SSBool "e",
              v4,
              v4',
              VSized.cons
                (Just $ ITE (SSBool "e") (SSBool "a") (SSBool "c"))
                (VSized.singleton (Just $ ITE (SSBool "e") (SSBool "b") (SSBool "d")))
            )
          ]
