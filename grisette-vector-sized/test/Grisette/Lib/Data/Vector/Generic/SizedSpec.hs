{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Lib.Data.Vector.Generic.SizedSpec where

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.Vector as V
import qualified Data.Vector.Generic.Sized as VSized
import Grisette.Core
import Grisette.Lib.Data.Vector.Generic.Sized ()
import Grisette.TestUtils.Mergeable
import Grisette.TestUtils.SBool
import Test.Hspec
import Test.Hspec.QuickCheck

spec :: Spec
spec = do
  describe "Mergeable for Sized Vector" $ do
    it "Mergeable for Sized Vector with zero length" $ do
      testMergeableSimpleEquivClass
        (VSized.empty :: VSized.Vector V.Vector 0 Integer)
        []
        [(SSBool "a", VSized.empty, VSized.empty, VSized.empty)]
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
        mergeStrategy
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
        [DynamicOrderedIdx $ buildStrategyList @SBool mergeStrategy v]
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
        [DynamicOrderedIdx $ buildStrategyList @SBool mergeStrategy v1]
        [(SSBool "a", v1, v1, v1)]
      testMergeableSimpleEquivClass
        v2
        [DynamicOrderedIdx $ buildStrategyList @SBool mergeStrategy v2]
        [(SSBool "c", v2, v2', VSized.cons (Just $ ITE (SSBool "c") (SSBool "a") (SSBool "b")) (VSized.singleton Nothing))]
      testMergeableSimpleEquivClass
        v3
        [DynamicOrderedIdx $ buildStrategyList @SBool mergeStrategy v3]
        [(SSBool "c", v3, v3', VSized.cons Nothing (VSized.singleton (Just $ ITE (SSBool "c") (SSBool "a") (SSBool "b"))))]
      testMergeableSimpleEquivClass
        v4
        [DynamicOrderedIdx $ buildStrategyList @SBool mergeStrategy v4]
        [ ( SSBool "e",
            v4,
            v4',
            VSized.cons
              (Just $ ITE (SSBool "e") (SSBool "a") (SSBool "c"))
              (VSized.singleton (Just $ ITE (SSBool "e") (SSBool "b") (SSBool "d")))
          )
        ]
  describe "SimpleMergeable for Sized Vector" $ do
    it "SimpleMergeable for Sized Vector with zero length" $ do
      mrgIte
        (SSBool "a")
        (VSized.empty :: VSized.Vector V.Vector 0 Integer)
        (VSized.empty :: VSized.Vector V.Vector 0 Integer)
        `shouldBe` (VSized.empty :: VSized.Vector V.Vector 0 Integer)
    it "SimpleMergeable for Sized Vector with simple mergeable contents" $ do
      mrgIte
        (SSBool "a")
        (VSized.cons (SSBool "b") (VSized.cons (SSBool "c") VSized.empty) :: VSized.Vector V.Vector 2 SBool)
        (VSized.cons (SSBool "d") (VSized.cons (SSBool "e") VSized.empty) :: VSized.Vector V.Vector 2 SBool)
        `shouldBe` ( VSized.cons
                       (ITE (SSBool "a") (SSBool "b") (SSBool "d"))
                       (VSized.cons (ITE (SSBool "a") (SSBool "c") (SSBool "e")) VSized.empty) ::
                       VSized.Vector V.Vector 2 SBool
                   )
  describe "Evaluate for Sized Vector" $ do
    it "Evaluate for Sized Vector" $ do
      let model = M.fromList [(SSymbol "a", True), (SSymbol "b", False)]
      evaluate
        False
        model
        ( VSized.cons (SSBool "a") $ VSized.cons (SSBool "c") $ VSized.cons (SSBool "b") VSized.empty ::
            VSized.Vector V.Vector 3 SBool
        )
        `shouldBe` VSized.cons (CBool True) (VSized.cons (SSBool "c") $ VSized.cons (CBool False) VSized.empty)
      evaluate
        True
        model
        ( VSized.cons (SSBool "a") $ VSized.cons (SSBool "c") $ VSized.cons (SSBool "b") VSized.empty ::
            VSized.Vector V.Vector 3 SBool
        )
        `shouldBe` VSized.cons (CBool True) (VSized.cons (CBool False) $ VSized.cons (CBool False) VSized.empty)
  describe "ExtractSymbolics for Sized Vector" $ do
    it "ExtractSymbolics for Sized Vector" $ do
      extractSymbolics
        ( VSized.cons (SSBool "a") $ VSized.cons (SSBool "c") $ VSized.cons (SSBool "b") VSized.empty ::
            VSized.Vector V.Vector 3 SBool
        )
        `shouldBe` S.fromList [SSymbol "a", SSymbol "b", SSymbol "c"]
  let v3a =
        ( VSized.cons (SSBool "a") $ VSized.cons (SSBool "b") $ VSized.cons (SSBool "c") VSized.empty ::
            VSized.Vector V.Vector 3 SBool
        )
  let v3b =
        ( VSized.cons (SSBool "d") $ VSized.cons (SSBool "e") $ VSized.cons (SSBool "f") VSized.empty ::
            VSized.Vector V.Vector 3 SBool
        )
  let l3a = [SSBool "a", SSBool "b", SSBool "c"]
  let l3b = [SSBool "d", SSBool "e", SSBool "f"]
  let v2c =
        ( VSized.cons (CBool True) $ VSized.cons (CBool False) VSized.empty ::
            VSized.Vector V.Vector 2 SBool
        )
  let v2s =
        ( VSized.cons (CBool True) $ VSized.cons (SSBool "a") VSized.empty ::
            VSized.Vector V.Vector 2 SBool
        )
  let v2cc =
        ( VSized.cons True $ VSized.cons False VSized.empty ::
            VSized.Vector V.Vector 2 Bool
        )
  describe "SEq for Sized Vector" $ do
    it "SEq for Sized Vector" $ do
      v3a ==~ v3b `shouldBe` (l3a ==~ l3b :: SBool)
  describe "SOrd for Sized Vector" $ do
    it "SOrd for Sized Vector" $ do
      v3a <=~ v3b `shouldBe` (l3a <=~ l3b :: SBool)
      v3a <~ v3b `shouldBe` (l3a <~ l3b :: SBool)
      v3a >=~ v3b `shouldBe` (l3a >=~ l3b :: SBool)
      v3a >~ v3b `shouldBe` (l3a >~ l3b :: SBool)
      v3a `symCompare` v3b `shouldBe` (l3a `symCompare` l3b :: UnionMBase SBool Ordering)
  describe "ToCon for Sized Vector" $ do
    it "ToCon for Sized Vector" $ do
      toCon v2c `shouldBe` Just v2cc
      toCon v2s `shouldBe` (Nothing :: Maybe (VSized.Vector V.Vector 2 Bool))
  describe "ToSym for Sized Vector" $ do
    it "ToSym for Sized Vector" $ do
      toSym v2cc `shouldBe` v2c 

