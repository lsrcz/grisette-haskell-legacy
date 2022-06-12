module Grisette.Lib.Control.Monad.TransSpec where

import Control.Monad.Except
import Grisette.Core.Control.Monad.UnionMBase
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.Lib.Control.Monad.Trans
import Grisette.TestUtils.SBool
import Test.Hspec

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
        `shouldBe` mrgSingle (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
