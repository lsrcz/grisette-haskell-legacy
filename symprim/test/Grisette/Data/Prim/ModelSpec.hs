module Grisette.Data.Prim.ModelSpec where

import qualified Data.BitVector.Sized.Signed as BVS
import qualified Data.BitVector.Sized.Unsigned as BVU
import Data.Data
import Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.Model as Model
import Grisette.Data.Prim.ModelValue
import Test.Hspec
import Grisette.Data.Prim.Num
import Grisette.Data.Prim.Bool

spec :: Spec
spec = do
  describe "empty model" $ do
    let m1 = Model.empty
    let m2 = Model.insert m1 (TermSymbol (Proxy @Integer) (SimpleSymbol "a")) (1 :: Integer)
    let m3 = Model.insert m2 (TermSymbol (Proxy @Bool) (SimpleSymbol "b")) True
    it "empty model is really empty" $ do
      Model.empty `shouldBe` Model M.empty
    it "inserting to model" $ do
      m3
        `shouldBe` Model
          ( M.fromList
              [ (SimpleSymbol "a", toModelValue (1 :: Integer)),
                (SimpleSymbol "b", toModelValue True)
              ]
          )
    it "valueOf" $ do
      valueOf m3 (SimpleSymbol "a") `shouldBe` Just (1 :: Integer)
      valueOf m3 (SimpleSymbol "b") `shouldBe` Just True
      valueOf m3 (SimpleSymbol "c") `shouldBe` (Nothing :: Maybe Integer)
    it "exceptFor" $ do
      exceptFor m3 (S.fromList [TermSymbol (Proxy @Integer) $ SimpleSymbol "a"])
        `shouldBe` Model
          ( M.fromList
              [ (SimpleSymbol "b", toModelValue True)
              ]
          )
    it "restrictTo" $ do
      restrictTo m3 (S.fromList [TermSymbol (Proxy @Integer) $ SimpleSymbol "a"])
        `shouldBe` Model
          ( M.fromList
              [ (SimpleSymbol "a", toModelValue (1 :: Integer))
              ]
          )
    it "extendTo" $ do
      extendTo
        m3
        ( S.fromList
            [ TermSymbol (Proxy @Integer) $ SimpleSymbol "c",
              TermSymbol (Proxy @Bool) $ SimpleSymbol "d",
              TermSymbol (Proxy @(BVU.UnsignedBV 4)) $ SimpleSymbol "e",
              TermSymbol (Proxy @(BVS.SignedBV 4)) $ SimpleSymbol "f"
            ]
        )
        `shouldBe` Model
          ( M.fromList
              [ (SimpleSymbol "a", toModelValue (1 :: Integer)),
                (SimpleSymbol "b", toModelValue True),
                (SimpleSymbol "c", toModelValue (0 :: Integer)),
                (SimpleSymbol "d", toModelValue False),
                (SimpleSymbol "e", toModelValue (0 :: BVU.UnsignedBV 4)),
                (SimpleSymbol "f", toModelValue (0 :: BVS.SignedBV 4))
              ]
          )
    it "exact" $ do
      exact
        m3
        ( S.fromList
            [ TermSymbol (Proxy @Integer) $ SimpleSymbol "a",
              TermSymbol (Proxy @Integer) $ SimpleSymbol "c"
            ]
        )
        `shouldBe` Model
          ( M.fromList
              [ (SimpleSymbol "a", toModelValue (1 :: Integer)),
                (SimpleSymbol "c", toModelValue (0 :: Integer))
              ]
          )
    it "evaluateTerm" $ do
      evaluateTerm False m3 (concTerm (1 :: Integer)) `shouldBe` concTerm 1
      evaluateTerm True m3 (concTerm (1 :: Integer)) `shouldBe` concTerm 1
      evaluateTerm False m3 (ssymbTerm "a" :: Term Integer) `shouldBe` concTerm 1
      evaluateTerm True m3 (ssymbTerm "a" :: Term Integer) `shouldBe` concTerm 1
      evaluateTerm False m3 (ssymbTerm "x" :: Term Integer) `shouldBe` ssymbTerm "x"
      evaluateTerm True m3 (ssymbTerm "x" :: Term Integer) `shouldBe` concTerm 0
      evaluateTerm False m3 (ssymbTerm "y" :: Term Bool) `shouldBe` ssymbTerm "y"
      evaluateTerm True m3 (ssymbTerm "y" :: Term Bool) `shouldBe` concTerm False
      evaluateTerm False m3 (ssymbTerm "z" :: Term (BVU.UnsignedBV 4)) `shouldBe` ssymbTerm "z"
      evaluateTerm True m3 (ssymbTerm "z" :: Term (BVU.UnsignedBV 4)) `shouldBe` concTerm 0
      evaluateTerm False m3 (uminusNum $ ssymbTerm "a" :: Term Integer) `shouldBe` concTerm (-1)
      evaluateTerm True m3 (uminusNum $ ssymbTerm "a" :: Term Integer) `shouldBe` concTerm (-1)
      evaluateTerm False m3 (uminusNum $ ssymbTerm "x" :: Term Integer) `shouldBe` uminusNum (ssymbTerm "x")
      evaluateTerm True m3 (uminusNum $ ssymbTerm "x" :: Term Integer) `shouldBe` concTerm 0
      evaluateTerm False m3 (addNum (ssymbTerm "a") (ssymbTerm "a") :: Term Integer) `shouldBe` concTerm 2
      evaluateTerm True m3 (addNum (ssymbTerm "a") (ssymbTerm "a") :: Term Integer) `shouldBe` concTerm 2
      evaluateTerm False m3 (addNum (ssymbTerm "x") (ssymbTerm "a") :: Term Integer) `shouldBe` addNum (concTerm 1) (ssymbTerm "x")
      evaluateTerm True m3 (addNum (ssymbTerm "x") (ssymbTerm "a") :: Term Integer) `shouldBe` concTerm 1
      evaluateTerm False m3 (addNum (ssymbTerm "x") (ssymbTerm "y") :: Term Integer) `shouldBe` addNum (ssymbTerm "x") (ssymbTerm "y") 
      evaluateTerm True m3 (addNum (ssymbTerm "x") (ssymbTerm "y") :: Term Integer) `shouldBe` concTerm 0
      evaluateTerm False m3 (iteterm (ssymbTerm "b") (addNum (ssymbTerm "a") (ssymbTerm "a")) (ssymbTerm "a") :: Term Integer)
        `shouldBe` concTerm 2
      evaluateTerm True m3 (iteterm (ssymbTerm "b") (addNum (ssymbTerm "a") (ssymbTerm "a")) (ssymbTerm "a") :: Term Integer)
        `shouldBe` concTerm 2
      evaluateTerm False m3 (iteterm (ssymbTerm "x") (addNum (ssymbTerm "a") (ssymbTerm "a")) (ssymbTerm "a") :: Term Integer)
        `shouldBe` iteterm (ssymbTerm "x") (concTerm 2) (concTerm 1)
      evaluateTerm True m3 (iteterm (ssymbTerm "x") (addNum (ssymbTerm "a") (ssymbTerm "a")) (ssymbTerm "a") :: Term Integer)
        `shouldBe` concTerm 1
      evaluateTerm False m3 (iteterm (ssymbTerm "b") (ssymbTerm "x") (addNum (concTerm 1) (ssymbTerm "y")) :: Term Integer)
        `shouldBe` ssymbTerm "x"
      evaluateTerm True m3 (iteterm (ssymbTerm "b") (ssymbTerm "x") (addNum (concTerm 1) (ssymbTerm "y")) :: Term Integer)
        `shouldBe` concTerm 0
      evaluateTerm False m3 (iteterm (ssymbTerm "z") (ssymbTerm "x") (addNum (concTerm 1) (ssymbTerm "y")) :: Term Integer)
        `shouldBe` iteterm (ssymbTerm "z") (ssymbTerm "x") (addNum (concTerm 1) (ssymbTerm "y"))
      evaluateTerm True m3 (iteterm (ssymbTerm "z") (ssymbTerm "x") (addNum (concTerm 1) (ssymbTerm "y")) :: Term Integer)
        `shouldBe` concTerm 1