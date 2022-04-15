module Grisette.Control.MonadSpec where

import Control.Monad.Coroutine hiding (merge)
import Control.Monad.Coroutine.SuspensionFunctors
import Control.Monad.Except hiding (guard)
import Control.Monad.Identity hiding (guard)
import Control.Monad.Reader hiding (guard)
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.UnionOp
import Test.Hspec
import Utils.SBool

spec :: Spec
spec = do
  describe "getSingle" $ do
    it "getSingle should work" $ do
      getSingle (guard (SSBool "a") (single $ SSBool "b") (single $ SSBool "c") :: UnionMBase SBool SBool)
        `shouldBe` ITE (SSBool "a") (SSBool "b") (SSBool "c")
  describe "MonadUnion for MaybeT" $ do
    it "merge should work" $ do
      merge
        ( MaybeT
            ( guard (SSBool "a") (single $ Just $ SSBool "b") (single $ Just $ SSBool "c") ::
                UnionMBase SBool (Maybe SBool)
            )
        )
        `shouldBe` MaybeT (mrgReturn $ Just $ ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    it "mrgReturn should work" $ do
      (mrgReturn 1 :: MaybeT (UnionMBase SBool) Integer) `shouldBe` MaybeT (mrgReturn $ Just 1)
    it "mrgIf should work" $
      do
        mrgIf (SSBool "a") (mrgReturn $ SSBool "b") (mrgReturn $ SSBool "c")
        `shouldBe` MaybeT
          ( mrgReturn $ Just $ ITE (SSBool "a") (SSBool "b") (SSBool "c") ::
              UnionMBase SBool (Maybe SBool)
          )
  describe "MonadUnion for ExceptT" $ do
    it "merge should work" $ do
      merge
        ( ExceptT
            ( guard (SSBool "a") (single $ Left $ SSBool "b") (single $ Left $ SSBool "c") ::
                UnionMBase SBool (Either SBool SBool)
            )
        )
        `shouldBe` ExceptT (mrgReturn $ Left $ ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    it "mrgReturn should work" $ do
      (mrgReturn 1 :: ExceptT SBool (UnionMBase SBool) Integer) `shouldBe` ExceptT (mrgReturn $ Right 1)
    it "mrgIf should work" $
      do
        mrgIf (SSBool "a") (mrgReturn $ SSBool "b") (mrgReturn $ SSBool "c")
        `shouldBe` ExceptT
          ( mrgReturn $ Right $ ITE (SSBool "a") (SSBool "b") (SSBool "c") ::
              UnionMBase SBool (Either SBool SBool)
          )
  describe "MonadUnion for Coroutine" $ do
    it "merge should work" $ do
      let Coroutine v =
            merge
              ( Coroutine $
                  guard
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
  describe "MonadUnion for StateT lazy" $ do
    it "merge should work" $ do
      let s :: StateLazy.StateT SBool (UnionMBase SBool) SBool =
            merge $ StateLazy.StateT $ \(x :: SBool) -> guard (SSBool "a") (single (x, Not x)) (single (Not x, x))
      StateLazy.runStateT s (SSBool "b")
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"),
            ITE (SSBool "a") (Not $ SSBool "b") (SSBool "b")
          )
    it "mrgReturn should work" $ do
      let s :: StateLazy.StateT SBool (UnionMBase SBool) SBool = mrgReturn (SSBool "x")
      StateLazy.runStateT s (SSBool "b") `shouldBe` mrgReturn (SSBool "x", SSBool "b")
    it "mrgIf should work" $ do
      let s :: StateLazy.StateT SBool (UnionMBase SBool) SBool =
            mrgIf
              (SSBool "a")
              (StateLazy.StateT $ \(x :: SBool) -> single (x, Not x))
              (StateLazy.StateT $ \(x :: SBool) -> single (Not x, x))
      StateLazy.runStateT s (SSBool "b")
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"),
            ITE (SSBool "a") (Not $ SSBool "b") (SSBool "b")
          )
  describe "MonadUnion for StateT strict" $ do
    it "merge should work" $ do
      let s :: StateStrict.StateT SBool (UnionMBase SBool) SBool =
            merge $ StateStrict.StateT $ \(x :: SBool) -> guard (SSBool "a") (single (x, Not x)) (single (Not x, x))
      StateStrict.runStateT s (SSBool "b")
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"),
            ITE (SSBool "a") (Not $ SSBool "b") (SSBool "b")
          )
    it "mrgReturn should work" $ do
      let s :: StateStrict.StateT SBool (UnionMBase SBool) SBool = mrgReturn (SSBool "x")
      StateStrict.runStateT s (SSBool "b") `shouldBe` mrgReturn (SSBool "x", SSBool "b")
    it "mrgIf should work" $ do
      let s :: StateStrict.StateT SBool (UnionMBase SBool) SBool =
            mrgIf
              (SSBool "a")
              (StateStrict.StateT $ \(x :: SBool) -> single (x, Not x))
              (StateStrict.StateT $ \(x :: SBool) -> single (Not x, x))
      StateStrict.runStateT s (SSBool "b")
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"),
            ITE (SSBool "a") (Not $ SSBool "b") (SSBool "b")
          )
  describe "MonadUnion for WriterT lazy" $ do
    it "merge should work" $ do
      let s :: WriterLazy.WriterT [SBool] (UnionMBase SBool) SBool =
            merge $
              WriterLazy.WriterT $
                guard
                  (SSBool "a")
                  (single (SSBool "b", [SSBool "c"]))
                  (single (SSBool "d", [SSBool "e"]))
      WriterLazy.runWriterT s
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (SSBool "d"),
            [ITE (SSBool "a") (SSBool "c") (SSBool "e")]
          )
    it "mrgReturn should work" $ do
      let s :: WriterLazy.WriterT [SBool] (UnionMBase SBool) SBool = mrgReturn (SSBool "x")
      WriterLazy.runWriterT s `shouldBe` mrgReturn (SSBool "x", [])
    it "mrgIf should work" $ do
      let s :: WriterLazy.WriterT [SBool] (UnionMBase SBool) SBool =
            mrgIf
              (SSBool "a")
              (WriterLazy.WriterT $ single (SSBool "b", [SSBool "c"]))
              (WriterLazy.WriterT $ single (SSBool "d", [SSBool "e"]))
      WriterLazy.runWriterT s
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (SSBool "d"),
            [ITE (SSBool "a") (SSBool "c") (SSBool "e")]
          )
  describe "MonadUnion for WriterT Strict" $ do
    it "merge should work" $ do
      let s :: WriterStrict.WriterT [SBool] (UnionMBase SBool) SBool =
            merge $
              WriterStrict.WriterT $
                guard
                  (SSBool "a")
                  (single (SSBool "b", [SSBool "c"]))
                  (single (SSBool "d", [SSBool "e"]))
      WriterStrict.runWriterT s
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (SSBool "d"),
            [ITE (SSBool "a") (SSBool "c") (SSBool "e")]
          )
    it "mrgReturn should work" $ do
      let s :: WriterStrict.WriterT [SBool] (UnionMBase SBool) SBool = mrgReturn (SSBool "x")
      WriterStrict.runWriterT s `shouldBe` mrgReturn (SSBool "x", [])
    it "mrgIf should work" $ do
      let s :: WriterStrict.WriterT [SBool] (UnionMBase SBool) SBool =
            mrgIf
              (SSBool "a")
              (WriterStrict.WriterT $ single (SSBool "b", [SSBool "c"]))
              (WriterStrict.WriterT $ single (SSBool "d", [SSBool "e"]))
      WriterStrict.runWriterT s
        `shouldBe` mrgReturn
          ( ITE (SSBool "a") (SSBool "b") (SSBool "d"),
            [ITE (SSBool "a") (SSBool "c") (SSBool "e")]
          )
  describe "MonadUnion for ReaderT" $ do
    it "merge should work" $ do
      let s :: ReaderT SBool (UnionMBase SBool) SBool =
            merge $ ReaderT $ \(x :: SBool) -> guard (SSBool "a") (single x) (single $ Not x)
      runReaderT s (SSBool "b")
        `shouldBe` mrgReturn
          (ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"))
    it "mrgReturn should work" $ do
      let s :: ReaderT SBool (UnionMBase SBool) SBool = mrgReturn (SSBool "x")
      runReaderT s (SSBool "b") `shouldBe` mrgReturn (SSBool "x")
    it "mrgIf should work" $ do
      let s :: ReaderT SBool (UnionMBase SBool) SBool =
            mrgIf
              (SSBool "a")
              (ReaderT $ \(x :: SBool) -> single x)
              (ReaderT $ \(x :: SBool) -> single $ Not x)
      runReaderT s (SSBool "b")
        `shouldBe` mrgReturn
          (ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"))
  describe "MonadUnion for IdentityT" $ do
    it "merge should work" $ do
      let s :: IdentityT (UnionMBase SBool) SBool =
            merge $
              IdentityT $
                guard
                  (SSBool "a")
                  (single $ SSBool "b")
                  (single $ SSBool "c")
      runIdentityT s `shouldBe` mrgReturn (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    it "mrgReturn should work" $ do
      let s :: IdentityT (UnionMBase SBool) SBool = mrgReturn (SSBool "x")
      runIdentityT s `shouldBe` mrgReturn (SSBool "x")
    it "mrgIf should work" $ do
      let s :: IdentityT (UnionMBase SBool) SBool =
            mrgIf
              (SSBool "a")
              (IdentityT $ single (SSBool "b"))
              (IdentityT $ single (SSBool "c"))
      runIdentityT s `shouldBe` mrgReturn (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
  describe "mrgFoldM" $ do
    it "mrgFoldM should work" $ do
      ( mrgFoldM
          (\acc (c, v) -> guard c (single $ acc + v) (single $ acc * v))
          10
          [(SSBool "a", 2), (SSBool "b", 3)] ::
          UnionMBase SBool Integer
        )
        `shouldBe` mrgIf
          (SSBool "a")
          (mrgIf (SSBool "b") (mrgReturn 15) (mrgReturn 36))
          (mrgIf (SSBool "b") (mrgReturn 23) (mrgReturn 60))
  describe "mrgMzero" $ do
    it "mrgMzero should work" $ do
      (mrgMzero :: MaybeT (UnionMBase SBool) Integer) `shouldBe` MaybeT (mrgReturn Nothing)
  describe "mrgMplus" $ do
    it "mrgMplus should work" $ do
      (mrgMzero `mrgMplus` mrgMzero :: MaybeT (UnionMBase SBool) Integer) `shouldBe` MaybeT (mrgReturn Nothing)
      (mrgReturn 1 `mrgMplus` mrgMzero :: MaybeT (UnionMBase SBool) Integer)
        `shouldBe` mrgReturn 1
      (mrgMzero `mrgMplus` mrgReturn 1 :: MaybeT (UnionMBase SBool) Integer)
        `shouldBe` mrgReturn 1
      (mrgReturn 2 `mrgMplus` mrgReturn 1 :: MaybeT (UnionMBase SBool) Integer)
        `shouldBe` mrgReturn 2
  describe "mrgMsum" $ do
    it "mrgMsum should work" $ do
      (mrgMsum [mrgMzero, mrgMzero] :: MaybeT (UnionMBase SBool) Integer) `shouldBe` mrgMzero
      (mrgMsum [mrgReturn 1, mrgMzero] :: MaybeT (UnionMBase SBool) Integer) `shouldBe` mrgReturn 1
      (mrgMsum [mrgMzero, mrgReturn 1] :: MaybeT (UnionMBase SBool) Integer) `shouldBe` mrgReturn 1
      (mrgMsum [mrgReturn 2, mrgReturn 1] :: MaybeT (UnionMBase SBool) Integer) `shouldBe` mrgReturn 2
  describe "mrgFmap" $ do
    it "mrgFmap should work" $ do
      mrgFmap (\x -> x * x) (mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn $ 1) :: UnionMBase SBool Integer)
        `shouldBe` mrgReturn 1
  describe ">>=~" $ do
    it ">>=~ should work" $ do
      guard (SSBool "a") (single $ -1) (single 1) >>=~ (\x -> return $ x * x)
        `shouldBe` (mrgReturn 1 :: UnionMBase SBool Integer)
  describe ">>~" $ do
    it ">>~ should work" $ do
      (guard (SSBool "a") (single $ -1) (single 1) :: UnionMBase SBool Integer)
        >>~ guard (SSBool "a") (single $ -1) (single 1)
        `shouldBe` (mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn 1) :: UnionMBase SBool Integer)
