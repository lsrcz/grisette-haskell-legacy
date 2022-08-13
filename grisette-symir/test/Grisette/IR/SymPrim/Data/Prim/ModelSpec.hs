{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.IR.SymPrim.Data.Prim.ModelSpec where

import Data.Data
import Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Grisette.IR.SymPrim.Data.BV
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.Model as Model
import Grisette.IR.SymPrim.Data.Prim.ModelValue
import Grisette.IR.SymPrim.Data.Prim.Num
import Test.Hspec

spec :: Spec
spec = do
  describe "empty model" $ do
    let asymbol = TermSymbol (Proxy @Integer) (SimpleSymbol "a")
    let bsymbol = TermSymbol (Proxy @Bool) (SimpleSymbol "b")
    let csymbol = TermSymbol (Proxy @Integer) (SimpleSymbol "c")
    let dsymbol = TermSymbol (Proxy @Bool) $ SimpleSymbol "d"
    let esymbol = TermSymbol (Proxy @(WordN 4)) $ SimpleSymbol "e"
    let fsymbol = TermSymbol (Proxy @(IntN 4)) $ SimpleSymbol "f"
    let m1 = Model.empty
    let m2 = Model.insert m1 asymbol (1 :: Integer)
    let m3 = Model.insert m2 bsymbol True
    it "empty model is really empty" $ do
      Model.empty `shouldBe` Model M.empty
    it "inserting to model" $ do
      m3
        `shouldBe` Model
          ( M.fromList
              [ (asymbol, toModelValue (1 :: Integer)),
                (bsymbol, toModelValue True)
              ]
          )
    it "equation" $ do
      equation m3 asymbol `shouldBe` Just (eqterm (ssymbTerm "a") (concTerm 1 :: Term Integer))
      equation m3 bsymbol `shouldBe` Just (eqterm (ssymbTerm "b") (concTerm True))
      equation m3 csymbol `shouldBe` Nothing
    it "valueOf" $ do
      valueOf m3 asymbol `shouldBe` Just (1 :: Integer)
      valueOf m3 bsymbol `shouldBe` Just True
      valueOf m3 csymbol `shouldBe` (Nothing :: Maybe Integer)
    it "exceptFor" $ do
      exceptFor m3 (S.fromList [asymbol])
        `shouldBe` Model
          ( M.fromList
              [ (bsymbol, toModelValue True)
              ]
          )
    it "restrictTo" $ do
      restrictTo m3 (S.fromList [asymbol])
        `shouldBe` Model
          ( M.fromList
              [ (asymbol, toModelValue (1 :: Integer))
              ]
          )
    it "extendTo" $ do
      extendTo
        m3
        ( S.fromList
            [ csymbol,
              dsymbol,
              esymbol,
              fsymbol
            ]
        )
        `shouldBe` Model
          ( M.fromList
              [ (asymbol, toModelValue (1 :: Integer)),
                (bsymbol, toModelValue True),
                (csymbol, toModelValue (0 :: Integer)),
                (dsymbol, toModelValue False),
                (esymbol, toModelValue (0 :: WordN 4)),
                (fsymbol, toModelValue (0 :: IntN 4))
              ]
          )
    it "exact" $ do
      exact
        m3
        ( S.fromList
            [ asymbol,
              csymbol
            ]
        )
        `shouldBe` Model
          ( M.fromList
              [ (asymbol, toModelValue (1 :: Integer)),
                (csymbol, toModelValue (0 :: Integer))
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
      evaluateTerm False m3 (ssymbTerm "z" :: Term (WordN 4)) `shouldBe` ssymbTerm "z"
      evaluateTerm True m3 (ssymbTerm "z" :: Term (WordN 4)) `shouldBe` concTerm 0
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
