{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Grisette.IR.SymPrim.Data.TabularFuncSpec where

import Grisette.Core.Data.Class.Function
import Grisette.IR.SymPrim.Data.TabularFunc
import Test.Hspec

spec :: Spec
spec = do
  describe "Tabular application" $ do
    it "Tabular application should work" $ do
      let f :: Integer =-> Integer = TabularFunc [(1, 2), (3, 4)] 5
      (f # 0) `shouldBe` 5
      (f # 1) `shouldBe` 2
      (f # 2) `shouldBe` 5
      (f # 3) `shouldBe` 4
      (f # 4) `shouldBe` 5
