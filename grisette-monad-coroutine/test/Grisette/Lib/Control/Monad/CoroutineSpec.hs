{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Lib.Control.Monad.CoroutineSpec where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Grisette.Lib.Control.Monad
import Grisette.Core
import Grisette.Lib.Control.Monad.Coroutine.SuspensionFunctors ()
import Grisette.TestUtils.SBool
import Test.Hspec

spec :: Spec
spec = do
  describe "MonadUnion for Coroutine" $ do
    it "merge should work" $ do
      let Coroutine v =
            merge
              ( Coroutine $
                  unionIf
                    (SSBool "a")
                    (single $ Left $ Yield (SSBool "b") $ Coroutine $ single $ Right $ SSBool "c")
                    (single $ Left $ Yield (SSBool "d") $ Coroutine $ single $ Right $ SSBool "e") ::
                  Coroutine (Yield SBool) (UnionMBase SBool) SBool
              )
      case v of
        SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
          x `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "d")
          y `shouldBe` ITE (SSBool "a") (SSBool "c") (SSBool "e")
        _ -> expectationFailure "Failed to merge Coroutine"
    it "mrgReturn should work" $ do
      case (mrgReturn 1 :: Coroutine (Yield SBool) (UnionMBase SBool) Integer) of
        Coroutine (SingleU (Right 1)) -> return ()
        _ -> expectationFailure "mrgReturn for Coroutine is not working"
    it "mrgIf should work" $ do
      let Coroutine v =
            mrgIf
              (SSBool "a")
              (Coroutine $ single $ Left $ Yield (SSBool "b") $ Coroutine $ single $ Right $ SSBool "c")
              (Coroutine $ single $ Left $ Yield (SSBool "d") $ Coroutine $ single $ Right $ SSBool "e") ::
              Coroutine (Yield SBool) (UnionMBase SBool) SBool
      case v of
        SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
          x `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "d")
          y `shouldBe` ITE (SSBool "a") (SSBool "c") (SSBool "e")
        _ -> expectationFailure "Failed to merge Coroutine"
  describe "Mergeable for Coroutine" $ do
    it "Mergeable for Coroutine should work" $ do
      let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool (Coroutine (Yield SBool) (UnionMBase SBool) SBool)
      let a1 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
            Coroutine (mrgReturn (Left (Yield (SSBool "a") (Coroutine (mrgReturn (Right $ SSBool "b"))))))
      let a2 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
            Coroutine (mrgReturn (Left (Yield (SSBool "c") (Coroutine (mrgReturn (Right $ SSBool "d"))))))
      let Coroutine r = s (SSBool "e") a1 a2
      case r of
        SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
          x `shouldBe` ITE (SSBool "e") (SSBool "a") (SSBool "c")
          y `shouldBe` ITE (SSBool "e") (SSBool "b") (SSBool "d")
        _ -> expectationFailure "Bad shape"
  describe "SimpleMergeable for Coroutine" $ do
    let a1 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
          Coroutine (mrgReturn (Left (Yield (SSBool "a") (Coroutine (mrgReturn (Right $ SSBool "b"))))))
    let a2 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
          Coroutine (mrgReturn (Left (Yield (SSBool "c") (Coroutine (mrgReturn (Right $ SSBool "d"))))))
    let Coroutine r = mrgIte (SSBool "e") a1 a2
    let Coroutine r1 = mrgIte1 (SSBool "e") a1 a2
    let Coroutine ru1 = mrgIf (SSBool "e") a1 a2
    it "SimpleMergeable for ExceptT should work" $ do
      case r of
        SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
          x `shouldBe` ITE (SSBool "e") (SSBool "a") (SSBool "c")
          y `shouldBe` ITE (SSBool "e") (SSBool "b") (SSBool "d")
        _ -> expectationFailure "Bad shape"
      case r1 of
        SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
          x `shouldBe` ITE (SSBool "e") (SSBool "a") (SSBool "c")
          y `shouldBe` ITE (SSBool "e") (SSBool "b") (SSBool "d")
        _ -> expectationFailure "Bad shape"
      case ru1 of
        SingleU (Left (Yield x (Coroutine (SingleU (Right y))))) -> do
          x `shouldBe` ITE (SSBool "e") (SSBool "a") (SSBool "c")
          y `shouldBe` ITE (SSBool "e") (SSBool "b") (SSBool "d")
        _ -> expectationFailure "Bad shape"