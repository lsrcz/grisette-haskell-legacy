{-# LANGUAGE ScopedTypeVariables #-}

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
import Grisette.Data.Class.Bool
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import Control.Monad.Identity

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
      it "SimpleMergeable for strict StateT should work" $ do
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
    describe "SimpleMergeable for WriterT" $ do
      it "SimpleMergeable for lazy WriterT should work" $ do
        let st1 :: WriterLazy.WriterT Integer (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgReturn (SSBool "a", 1)
        let st2 :: WriterLazy.WriterT Integer (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgReturn (SSBool "b", 2)
        let st3 :: WriterLazy.WriterT Integer (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgReturn (SSBool "c", 1)
        let st4 = mrgIte (SSBool "d") st1 st2
        let st41 = mrgIte1 (SSBool "d") st1 st2
        let st4u1 = mrgIteu1 (SSBool "d") st1 st2
        let st5 = mrgIte (SSBool "d") st1 st3
        let st51 = mrgIte1 (SSBool "d") st1 st3
        let st5u1 = mrgIteu1 (SSBool "d") st1 st3
        WriterLazy.runWriterT st4 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterLazy.runWriterT st41 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterLazy.runWriterT st4u1 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterLazy.runWriterT st5 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterLazy.runWriterT st51 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterLazy.runWriterT st5u1 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
      it "SimpleMergeable for strict WriterT should work" $ do
        let st1 :: WriterStrict.WriterT Integer (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgReturn (SSBool "a", 1)
        let st2 :: WriterStrict.WriterT Integer (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgReturn (SSBool "b", 2)
        let st3 :: WriterStrict.WriterT Integer (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgReturn (SSBool "c", 1)
        let st4 = mrgIte (SSBool "d") st1 st2
        let st41 = mrgIte1 (SSBool "d") st1 st2
        let st4u1 = mrgIteu1 (SSBool "d") st1 st2
        let st5 = mrgIte (SSBool "d") st1 st3
        let st51 = mrgIte1 (SSBool "d") st1 st3
        let st5u1 = mrgIteu1 (SSBool "d") st1 st3
        WriterStrict.runWriterT st4 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterStrict.runWriterT st41 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterStrict.runWriterT st4u1 `shouldBe` mrgIf (SSBool "d") (mrgReturn (SSBool "a", 1)) (mrgReturn (SSBool "b", 2))
        WriterStrict.runWriterT st5 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterStrict.runWriterT st51 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterStrict.runWriterT st5u1 `shouldBe` mrgReturn (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
    describe "SimpleMergeable for ReaderT" $ do
      it "SimpleMergeable for ReaderT should work" $ do
        let r1 :: ReaderT Integer (UnionMBase SBool) Integer =
              ReaderT $ \(x :: Integer) -> mrgReturn $ x + 2
        let r2 :: ReaderT Integer (UnionMBase SBool) Integer =
              ReaderT $ \(x :: Integer) -> mrgReturn $ x * 2
        let r3 = mrgIte (SSBool "c") r1 r2
        -- let r31 = mrgIte1 (SSBool "c") r1 r2
        let r3u1 = mrgIteu1 (SSBool "c") r1 r2
        runReaderT r3 2 `shouldBe` mrgReturn 4
        runReaderT r3 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn 5) (mrgReturn 6)
        -- runReaderT r31 2 `shouldBe` mrgReturn 4
        -- runReaderT r31 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn 5) (mrgReturn 6)
        runReaderT r3u1 2 `shouldBe` mrgReturn 4
        runReaderT r3u1 3 `shouldBe` mrgIf (SSBool "c") (mrgReturn 5) (mrgReturn 6)

        let r4 :: ReaderT SBool (UnionMBase SBool) SBool =
              ReaderT $ \x -> mrgReturn $ x &&~ (SSBool "x")
        let r5 :: ReaderT SBool (UnionMBase SBool) SBool =
              ReaderT $ \x -> mrgReturn $ x ||~ (SSBool "y")
        let r61 = mrgIte1 (SSBool "c") r4 r5
        runReaderT r61 (SSBool "a") `shouldBe` mrgReturn (ites (SSBool "c") (SSBool "a" &&~ SSBool "x") (SSBool "a" ||~ SSBool "y"))
    describe "SimpleMergeable for Identity" $ do
      it "SimpleMergeable for Identity should work" $ do
        let i1 :: Identity SBool = Identity $ SSBool "a"
        let i2 :: Identity SBool = Identity $ SSBool "b"
        let i3 = mrgIte (SSBool "c") i1 i2
        let i31 = mrgIte1 (SSBool "c") i1 i2
        runIdentity i3 `shouldBe` ITE (SSBool "c") (SSBool "a") (SSBool "b")
        runIdentity i31 `shouldBe` ITE (SSBool "c") (SSBool "a") (SSBool "b")
    describe "SimpleMergeable for IdentityT" $ do
      it "SimpleMergeable for IdentityT UnionM should work" $ do
        let i1 :: IdentityT (UnionMBase SBool) SBool = IdentityT $ mrgReturn $ SSBool "a"
        let i2 :: IdentityT (UnionMBase SBool) SBool = IdentityT $ mrgReturn $ SSBool "b"
        let i3 = mrgIte (SSBool "c") i1 i2
        let i31 = mrgIte1 (SSBool "c") i1 i2
        let i3u1 = mrgIteu1 (SSBool "c") i1 i2
        runIdentityT i3 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
        runIdentityT i31 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
        runIdentityT i3u1 `shouldBe` mrgReturn (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
