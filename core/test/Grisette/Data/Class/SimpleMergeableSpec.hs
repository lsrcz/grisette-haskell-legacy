module Grisette.Data.Class.SimpleMergeableSpec where

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.SimpleMergeable
import Test.Hspec
import Utils.SBool
import Control.Monad.Coroutine
import Control.Monad.Coroutine.SuspensionFunctors
import Grisette.Data.Class.UnionOp
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict

spec :: Spec
spec = do
  describe "SimpleMergeable for common types" $ do
    describe "SimpleMergeable for SBool" $ do
      it "SimpleMergeable for SBool should work" $ do
        mrgIte (SSBool "a") (SSBool "b") (SSBool "c") `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "c")
    describe "SimpleMergeable for ()" $ do
      it "SimpleMergeable for () should work" $ do
        mrgIte (SSBool "a") () () `shouldBe` ()
    describe "SimpleMergeable for (,)" $ do
      it "SimpleMergeable for (,) should work" $ do
        mrgIte (SSBool "a") (SSBool "b", SSBool "d") (SSBool "c", SSBool "e")
          `shouldBe` (ITE (SSBool "a") (SSBool "b") (SSBool "c"), ITE (SSBool "a") (SSBool "d") (SSBool "e"))
    describe "SimpleMergeable for (,,)" $ do
      it "SimpleMergeable for (,,) should work" $ do
        mrgIte (SSBool "a") (SSBool "b", SSBool "d", SSBool "f") (SSBool "c", SSBool "e", SSBool "g")
          `shouldBe` ( ITE (SSBool "a") (SSBool "b") (SSBool "c"),
                       ITE (SSBool "a") (SSBool "d") (SSBool "e"),
                       ITE (SSBool "a") (SSBool "f") (SSBool "g")
                     )
    describe "SimpleMergeable for (,,,)" $ do
      it "SimpleMergeable for (,,,) should work" $ do
        mrgIte
          (SSBool "a")
          (SSBool "b", SSBool "d", SSBool "f", SSBool "h")
          (SSBool "c", SSBool "e", SSBool "g", SSBool "i")
          `shouldBe` ( ITE (SSBool "a") (SSBool "b") (SSBool "c"),
                       ITE (SSBool "a") (SSBool "d") (SSBool "e"),
                       ITE (SSBool "a") (SSBool "f") (SSBool "g"),
                       ITE (SSBool "a") (SSBool "h") (SSBool "i")
                     )
    describe "SimpleMergeable for (,,,,)" $ do
      it "SimpleMergeable for (,,,,) should work" $ do
        mrgIte
          (SSBool "a")
          (SSBool "b", SSBool "d", SSBool "f", SSBool "h", SSBool "j")
          (SSBool "c", SSBool "e", SSBool "g", SSBool "i", SSBool "k")
          `shouldBe` ( ITE (SSBool "a") (SSBool "b") (SSBool "c"),
                       ITE (SSBool "a") (SSBool "d") (SSBool "e"),
                       ITE (SSBool "a") (SSBool "f") (SSBool "g"),
                       ITE (SSBool "a") (SSBool "h") (SSBool "i"),
                       ITE (SSBool "a") (SSBool "j") (SSBool "k")
                     )
    describe "SimpleMergeable for (,,,,,)" $ do
      it "SimpleMergeable for (,,,,,) should work" $ do
        mrgIte
          (SSBool "a")
          (SSBool "b", SSBool "d", SSBool "f", SSBool "h", SSBool "j", SSBool "l")
          (SSBool "c", SSBool "e", SSBool "g", SSBool "i", SSBool "k", SSBool "m")
          `shouldBe` ( ITE (SSBool "a") (SSBool "b") (SSBool "c"),
                       ITE (SSBool "a") (SSBool "d") (SSBool "e"),
                       ITE (SSBool "a") (SSBool "f") (SSBool "g"),
                       ITE (SSBool "a") (SSBool "h") (SSBool "i"),
                       ITE (SSBool "a") (SSBool "j") (SSBool "k"),
                       ITE (SSBool "a") (SSBool "l") (SSBool "m")
                     )
    describe "SimpleMergeable for (,,,,,,)" $ do
      it "SimpleMergeable for (,,,,,,) should work" $ do
        mrgIte
          (SSBool "a")
          (SSBool "b", SSBool "d", SSBool "f", SSBool "h", SSBool "j", SSBool "l", SSBool "n")
          (SSBool "c", SSBool "e", SSBool "g", SSBool "i", SSBool "k", SSBool "m", SSBool "o")
          `shouldBe` ( ITE (SSBool "a") (SSBool "b") (SSBool "c"),
                       ITE (SSBool "a") (SSBool "d") (SSBool "e"),
                       ITE (SSBool "a") (SSBool "f") (SSBool "g"),
                       ITE (SSBool "a") (SSBool "h") (SSBool "i"),
                       ITE (SSBool "a") (SSBool "j") (SSBool "k"),
                       ITE (SSBool "a") (SSBool "l") (SSBool "m"),
                       ITE (SSBool "a") (SSBool "n") (SSBool "o")
                     )
    describe "SimpleMergeable for (,,,,,,,)" $ do
      it "SimpleMergeable for (,,,,,,,) should work" $ do
        mrgIte
          (SSBool "a")
          (SSBool "b", SSBool "d", SSBool "f", SSBool "h", SSBool "j", SSBool "l", SSBool "n", SSBool "p")
          (SSBool "c", SSBool "e", SSBool "g", SSBool "i", SSBool "k", SSBool "m", SSBool "o", SSBool "q")
          `shouldBe` ( ITE (SSBool "a") (SSBool "b") (SSBool "c"),
                       ITE (SSBool "a") (SSBool "d") (SSBool "e"),
                       ITE (SSBool "a") (SSBool "f") (SSBool "g"),
                       ITE (SSBool "a") (SSBool "h") (SSBool "i"),
                       ITE (SSBool "a") (SSBool "j") (SSBool "k"),
                       ITE (SSBool "a") (SSBool "l") (SSBool "m"),
                       ITE (SSBool "a") (SSBool "n") (SSBool "o"),
                       ITE (SSBool "a") (SSBool "p") (SSBool "q")
                     )
    describe "SimpleMergeable for functions" $ do
      it "SimpleMergeable for functions should work" $ do
        let f = mrgIte (SSBool "a") Not (And (SSBool "b"))
        f (SSBool "c") `shouldBe` ITE (SSBool "a") (Not $ SSBool "c") (And (SSBool "b") (SSBool "c"))
    describe "SimpleMergeable for MaybeT" $ do
      let l :: MaybeT (UnionMBase SBool) SBool =
            MaybeT (mrgIf (SSBool "b") (mrgReturn Nothing) (mrgReturn $ Just $ SSBool "c"))
      let r :: MaybeT (UnionMBase SBool) SBool =
            MaybeT (mrgIf (SSBool "d") (mrgReturn Nothing) (mrgReturn $ Just $ SSBool "e"))
      let res :: MaybeT (UnionMBase SBool) SBool =
            MaybeT
              ( mrgIf
                  (SSBool "a")
                  (mrgIf (SSBool "b") (mrgReturn Nothing) (mrgReturn $ Just $ SSBool "c"))
                  (mrgIf (SSBool "d") (mrgReturn Nothing) (mrgReturn $ Just $ SSBool "e"))
              )

      it "SimpleMergeable for MaybeT should work" $ do
        mrgIte (SSBool "a") l r `shouldBe` res
        mrgIte1 (SSBool "a") l r `shouldBe` res
        mrgIteu1 (SSBool "a") l r `shouldBe` res
    describe "SimpleMergeable for ExceptT" $ do
      let l :: ExceptT SBool (UnionMBase SBool) SBool =
            ExceptT (mrgIf (SSBool "b") (mrgReturn $ Left $ SSBool "c") (mrgReturn $ Right $ SSBool "d"))
      let r = ExceptT (mrgIf (SSBool "e") (mrgReturn $ Left $ SSBool "f") (mrgReturn $ Right $ SSBool "g"))
      let res =
            ExceptT
              ( mrgIf
                  (SSBool "a")
                  (mrgIf (SSBool "b") (mrgReturn $ Left $ SSBool "c") (mrgReturn $ Right $ SSBool "d"))
                  (mrgIf (SSBool "e") (mrgReturn $ Left $ SSBool "f") (mrgReturn $ Right $ SSBool "g"))
              )
      it "SimpleMergeable for ExceptT should work" $ do
        mrgIte (SSBool "a") l r `shouldBe` res
    describe "SimpleMergeable for Coroutine" $ do
      let a1 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
            Coroutine (mrgReturn (Left (Yield (SSBool "a") (Coroutine (mrgReturn (Right $ SSBool "b"))))))
      let a2 :: Coroutine (Yield SBool) (UnionMBase SBool) SBool =
            Coroutine (mrgReturn (Left (Yield (SSBool "c") (Coroutine (mrgReturn (Right $ SSBool "d"))))))
      let Coroutine r = mrgIte (SSBool "e") a1 a2
      let Coroutine r1 = mrgIte1 (SSBool "e") a1 a2
      let Coroutine ru1 = mrgIteu1 (SSBool "e") a1 a2
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
    describe "SimpleMergeable for StateT" $ do
      it "SimpleMergeable for lazy StateT should work" $ do
        let st1 :: StateLazy.StateT Integer (UnionMBase SBool) SBool =
              StateLazy.StateT $ \(x :: Integer) -> mrgReturn (SSBool "a", x + 2)
        let st2 :: StateLazy.StateT Integer (UnionMBase SBool) SBool =
              StateLazy.StateT $ \(x :: Integer) -> mrgReturn (SSBool "b", x * 2)
        let st3 = mrgIte (SSBool "c") st1 st2
        let st31 = mrgIte1 (SSBool "c") st1 st2
        let st3u1 = mrgIteu1 (SSBool "c") st1 st2
        StateLazy.runStateT st3 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st3 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
        StateLazy.runStateT st31 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st31 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
        StateLazy.runStateT st3u1 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st3u1 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
      it "Mergeable for strict StateT should work" $ do
        let st1 :: StateStrict.StateT Integer (UnionMBase SBool) SBool =
              StateStrict.StateT $ \(x :: Integer) -> mrgReturn (SSBool "a", x + 2)
        let st2 :: StateStrict.StateT Integer (UnionMBase SBool) SBool =
              StateStrict.StateT $ \(x :: Integer) -> mrgReturn (SSBool "b", x * 2)
        let st3 = mrgIte (SSBool "c") st1 st2
        let st31 = mrgIte1 (SSBool "c") st1 st2
        let st3u1 = mrgIteu1 (SSBool "c") st1 st2
        StateStrict.runStateT st3 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st3 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
        StateStrict.runStateT st31 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st31 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))
        StateStrict.runStateT st3u1 2 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st3u1 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn (SSBool "a", 5)) (mrgReturn (SSBool "b", 6))