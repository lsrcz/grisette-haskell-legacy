module Grisette.Data.Prim.TabularFuncSpec where

import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.InternedTerm
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.TabularFunc
import Test.Hspec

spec :: Spec
spec = do
  describe "ApplyF" $ do
    it "ApplyF with concrete" $ do
      let f :: Integer =-> Integer =
            TabularFunc [(1, 2), (3, 4)] 5
      applyf (concTerm f) (concTerm 0) `shouldBe` concTerm 5
      applyf (concTerm f) (concTerm 1) `shouldBe` concTerm 2
      applyf (concTerm f) (concTerm 2) `shouldBe` concTerm 5
      applyf (concTerm f) (concTerm 3) `shouldBe` concTerm 4
      applyf (concTerm f) (concTerm 4) `shouldBe` concTerm 5
    it "ApplyF with concrete function" $ do
      let f :: Integer =-> Integer =
            TabularFunc [(1, 2), (3, 4)] 5
      applyf (concTerm f) (ssymbTerm "b")
        `shouldBe` iteterm
          (eqterm (concTerm 1 :: Term Integer) (ssymbTerm "b"))
          (concTerm 2)
          ( iteterm
              (eqterm (concTerm 3 :: Term Integer) (ssymbTerm "b"))
              (concTerm 4)
              (concTerm 5)
          )
    it "ApplyF with symbolic" $ do
      applyf (ssymbTerm "f" :: Term (Integer =-> Integer)) (ssymbTerm "a")
        `shouldBe` constructBinary
          ApplyF
          (ssymbTerm "f" :: Term (Integer =-> Integer))
          (ssymbTerm "a" :: Term Integer)
  describe "ApplyF pattern" $ do
      it "ApplyF pattern should work" $ do
        case ssymbTerm "a" :: Term Bool of
          ApplyFTerm _ (_ :: Term Bool) -> expectationFailure "Bad pattern matching"
          _ -> return ()
        case applyf (ssymbTerm "a" :: Term (Integer =-> Integer)) (ssymbTerm "b") of
          ApplyFTerm _ (_ :: Term Bool) -> do
            expectationFailure "Bad pattern matching"
          ApplyFTerm v1 (v2 :: Term Integer) -> do
            v1 `shouldBe` ssymbTerm "a"
            v2 `shouldBe` ssymbTerm "b"
          _ -> return ()

