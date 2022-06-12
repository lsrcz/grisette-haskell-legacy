module Grisette.Lib.Control.Monad.ExceptSpec where

import Control.Monad.Trans.Except
import Grisette.Lib.Control.Monad.Except
import Grisette.Core.Control.Monad.UnionMBase
import Grisette.Core.Data.Class.SimpleMergeable
import Test.Hspec
import Grisette.TestUtils.SBool

spec :: Spec
spec = do
  describe "mrgThrowError" $ do
    it "mrgThrowError should work" $
      runExceptT (mrgThrowError 1 :: ExceptT Integer (UnionMBase SBool) ())
        `shouldBe` mrgSingle (Left 1)
    it "mrgCatchError should work" $
      ( ExceptT (unionIf (SSBool "a") (return $ Left (SSBool "b")) (return $ Right (SSBool "c"))) ::
          ExceptT SBool (UnionMBase SBool) SBool
      )
        `mrgCatchError` return
          `shouldBe` mrgSingle (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
