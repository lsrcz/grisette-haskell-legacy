module Grisette.Control.Monad.TransSpec where

import Control.Monad.Except hiding (guard)
import Grisette.Control.Monad
import Grisette.Control.Monad.Trans
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.UnionOp
import Test.Hspec
import Utils.SBool

spec :: Spec
spec = do
  describe "mrgLift" $ do
    it "mrgLift should work" $ do
      ( mrgLift
          ( guard (SSBool "a") (single (SSBool "b")) (single (SSBool "c")) ::
              UnionMBase SBool SBool
          ) ::
          ExceptT SBool (UnionMBase SBool) SBool
        )
        `shouldBe` mrgReturn (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
