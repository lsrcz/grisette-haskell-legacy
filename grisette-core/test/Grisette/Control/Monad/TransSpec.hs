module Grisette.Control.Monad.TransSpec where

import Control.Monad.Except
import Grisette.Control.Monad.Union
import Grisette.Control.Monad.Trans
import Grisette.Control.Monad.UnionMBase
import Test.Hspec
import Grisette.TestUtils.SBool
import Grisette.Data.Class.SimpleMergeable

spec :: Spec
spec = do
  describe "mrgLift" $ do
    it "mrgLift should work" $ do
      ( mrgLift
          ( unionIf (SSBool "a") (single (SSBool "b")) (single (SSBool "c")) ::
              UnionMBase SBool SBool
          ) ::
          ExceptT SBool (UnionMBase SBool) SBool
        )
        `shouldBe` mrgReturn (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
