module Grisette.Control.Monad.ExceptSpec where

import Control.Monad.Trans.Except
import Grisette.Control.Monad.Except
import Grisette.Control.Monad.Union
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.UnionOp
import Test.Hspec
import Utils.SBool

spec :: Spec
spec = do
  describe "mrgThrowError" $ do
    it "mrgThrowError should work" $
      runExceptT (mrgThrowError 1 :: ExceptT Integer (UnionMBase SBool) ())
        `shouldBe` mrgReturn (Left 1)
    it "mrgCatchError should work" $
      ( ExceptT (guard (SSBool "a") (return $ Left (SSBool "b")) (return $ Right (SSBool "c"))) ::
          ExceptT SBool (UnionMBase SBool) SBool
      )
        `mrgCatchError` return
          `shouldBe` mrgReturn (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
