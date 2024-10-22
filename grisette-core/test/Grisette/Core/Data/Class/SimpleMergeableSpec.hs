{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Grisette.Core.Data.Class.SimpleMergeableSpec where

import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.Identity
import qualified Control.Monad.RWS.Lazy as RWSTLazy
import qualified Control.Monad.RWS.Strict as RWSTStrict
import Control.Monad.Reader
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import qualified Data.Monoid as Monoid
import GHC.Generics
import Generics.Deriving
import Grisette.Core.Control.Monad.UnionMBase
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.TestUtils.SBool
import Test.Hspec

newtype AndMonoidSBool = AndMonoidSBool SBool
  deriving (Show, Generic, Eq)
  deriving (Mergeable SBool) via (Default AndMonoidSBool)

instance Semigroup AndMonoidSBool where
  (AndMonoidSBool a) <> (AndMonoidSBool b) = AndMonoidSBool (And a b)

instance Monoid AndMonoidSBool where
  mempty = AndMonoidSBool $ CBool True

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
            MaybeT (mrgIf (SSBool "b") (mrgSingle Nothing) (mrgSingle $ Just $ SSBool "c"))
      let r :: MaybeT (UnionMBase SBool) SBool =
            MaybeT (mrgIf (SSBool "d") (mrgSingle Nothing) (mrgSingle $ Just $ SSBool "e"))
      let res :: MaybeT (UnionMBase SBool) SBool =
            MaybeT
              ( mrgIf
                  (SSBool "a")
                  (mrgIf (SSBool "b") (mrgSingle Nothing) (mrgSingle $ Just $ SSBool "c"))
                  (mrgIf (SSBool "d") (mrgSingle Nothing) (mrgSingle $ Just $ SSBool "e"))
              )

      it "SimpleMergeable for MaybeT should work" $ do
        mrgIte (SSBool "a") l r `shouldBe` res
        mrgIte1 (SSBool "a") l r `shouldBe` res
        mrgIf (SSBool "a") l r `shouldBe` res
    describe "SimpleMergeable for ExceptT" $ do
      let l :: ExceptT SBool (UnionMBase SBool) SBool =
            ExceptT (mrgIf (SSBool "b") (mrgSingle $ Left $ SSBool "c") (mrgSingle $ Right $ SSBool "d"))
      let r = ExceptT (mrgIf (SSBool "e") (mrgSingle $ Left $ SSBool "f") (mrgSingle $ Right $ SSBool "g"))
      let res =
            ExceptT
              ( mrgIf
                  (SSBool "a")
                  (mrgIf (SSBool "b") (mrgSingle $ Left $ SSBool "c") (mrgSingle $ Right $ SSBool "d"))
                  (mrgIf (SSBool "e") (mrgSingle $ Left $ SSBool "f") (mrgSingle $ Right $ SSBool "g"))
              )
      it "SimpleMergeable for ExceptT should work" $ do
        mrgIte (SSBool "a") l r `shouldBe` res
    describe "SimpleMergeable for StateT" $ do
      it "SimpleMergeable for lazy StateT should work" $ do
        let st1 :: StateLazy.StateT Integer (UnionMBase SBool) SBool =
              StateLazy.StateT $ \(x :: Integer) -> mrgSingle (SSBool "a", x + 2)
        let st2 :: StateLazy.StateT Integer (UnionMBase SBool) SBool =
              StateLazy.StateT $ \(x :: Integer) -> mrgSingle (SSBool "b", x * 2)
        let st3 = mrgIte (SSBool "c") st1 st2
        let st31 = mrgIte1 (SSBool "c") st1 st2
        let st3u1 = mrgIf (SSBool "c") st1 st2
        StateLazy.runStateT st3 2 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st3 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle (SSBool "a", 5)) (mrgSingle (SSBool "b", 6))
        StateLazy.runStateT st31 2 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st31 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle (SSBool "a", 5)) (mrgSingle (SSBool "b", 6))
        StateLazy.runStateT st3u1 2 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateLazy.runStateT st3u1 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle (SSBool "a", 5)) (mrgSingle (SSBool "b", 6))
      it "SimpleMergeable for strict StateT should work" $ do
        let st1 :: StateStrict.StateT Integer (UnionMBase SBool) SBool =
              StateStrict.StateT $ \(x :: Integer) -> mrgSingle (SSBool "a", x + 2)
        let st2 :: StateStrict.StateT Integer (UnionMBase SBool) SBool =
              StateStrict.StateT $ \(x :: Integer) -> mrgSingle (SSBool "b", x * 2)
        let st3 = mrgIte (SSBool "c") st1 st2
        let st31 = mrgIte1 (SSBool "c") st1 st2
        let st3u1 = mrgIf (SSBool "c") st1 st2
        StateStrict.runStateT st3 2 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st3 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle (SSBool "a", 5)) (mrgSingle (SSBool "b", 6))
        StateStrict.runStateT st31 2 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st31 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle (SSBool "a", 5)) (mrgSingle (SSBool "b", 6))
        StateStrict.runStateT st3u1 2 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"), 4)
        StateStrict.runStateT st3u1 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle (SSBool "a", 5)) (mrgSingle (SSBool "b", 6))
    describe "SimpleMergeable for ContT" $ do
      it "SimpleMergeable for ContT should work" $ do
        let c1 :: ContT (SBool, Integer) (UnionMBase SBool) (SBool, Integer) = ContT $ \f -> f (SSBool "a", 2)
        let c2 :: ContT (SBool, Integer) (UnionMBase SBool) (SBool, Integer) = ContT $ \f -> f (SSBool "b", 3)
        let c3 = mrgIte (SSBool "c") c1 c2
        let c3u1 = mrgIf (SSBool "c") c1 c2
        let r =
              mrgIf
                (SSBool "c")
                (mrgIf (SSBool "p") (mrgSingle (SSBool "a", 2)) (mrgSingle (Not $ SSBool "a", 3)))
                (mrgIf (SSBool "p") (mrgSingle (SSBool "b", 3)) (mrgSingle (Not $ SSBool "b", 4)))
        let f = (\(a, x) -> mrgIf (SSBool "p") (mrgSingle (a, x)) (mrgSingle (nots a, x + 1)))
        runContT c3 f `shouldBe` r
        runContT c3u1 f `shouldBe` r
    describe "SimpleMergeable for RWST" $ do
      it "SimpleMergeable for lazy RWST should work" $ do
        let rws1 ::
              RWSTLazy.RWST
                (Integer, SBool)
                (Monoid.Sum Integer, AndMonoidSBool)
                (Integer, SBool)
                (UnionMBase SBool)
                (Integer, SBool) =
                RWSTLazy.RWST $ \(ir, br) (is, bs) ->
                  mrgSingle ((ir + is, br &&~ bs), (ir - is, br ||~ bs), (Monoid.Sum $ ir * is, AndMonoidSBool $ bs &&~ br))
        let rws2 ::
              RWSTLazy.RWST
                (Integer, SBool)
                (Monoid.Sum Integer, AndMonoidSBool)
                (Integer, SBool)
                (UnionMBase SBool)
                (Integer, SBool) =
                RWSTLazy.RWST $ \(ir, br) (is, bs) ->
                  mrgSingle ((ir + is, br ||~ bs), (ir - is, br &&~ bs), (Monoid.Sum $ ir * is, AndMonoidSBool $ bs ||~ br))
        let rws3 = mrgIte (SSBool "c") rws1 rws2
        let rws3u1 = mrgIf (SSBool "c") rws1 rws2

        let res1 :: UnionMBase SBool ((Integer, SBool), (Integer, SBool), (Monoid.Sum Integer, AndMonoidSBool)) =
              mrgIf
                (SSBool "c")
                (mrgSingle ((1, And (SSBool "a") (SSBool "b")), (-1, Or (SSBool "a") (SSBool "b")), (0, AndMonoidSBool $ And (SSBool "b") (SSBool "a"))))
                (mrgSingle ((1, Or (SSBool "a") (SSBool "b")), (-1, And (SSBool "a") (SSBool "b")), (0, AndMonoidSBool $ Or (SSBool "b") (SSBool "a"))))
        RWSTLazy.runRWST rws3 (0, SSBool "a") (1, SSBool "b") `shouldBe` res1
        RWSTLazy.runRWST rws3u1 (0, SSBool "a") (1, SSBool "b") `shouldBe` res1
      it "SimpleMergeable for strict RWST should work" $ do
        let rws1 ::
              RWSTStrict.RWST
                (Integer, SBool)
                (Monoid.Sum Integer, AndMonoidSBool)
                (Integer, SBool)
                (UnionMBase SBool)
                (Integer, SBool) =
                RWSTStrict.RWST $ \(ir, br) (is, bs) ->
                  mrgSingle ((ir + is, br &&~ bs), (ir - is, br ||~ bs), (Monoid.Sum $ ir * is, AndMonoidSBool $ bs &&~ br))
        let rws2 ::
              RWSTStrict.RWST
                (Integer, SBool)
                (Monoid.Sum Integer, AndMonoidSBool)
                (Integer, SBool)
                (UnionMBase SBool)
                (Integer, SBool) =
                RWSTStrict.RWST $ \(ir, br) (is, bs) ->
                  mrgSingle ((ir + is, br ||~ bs), (ir - is, br &&~ bs), (Monoid.Sum $ ir * is, AndMonoidSBool $ bs ||~ br))
        let rws3 = mrgIte (SSBool "c") rws1 rws2
        let rws3u1 = mrgIf (SSBool "c") rws1 rws2

        let res1 :: UnionMBase SBool ((Integer, SBool), (Integer, SBool), (Monoid.Sum Integer, AndMonoidSBool)) =
              mrgIf
                (SSBool "c")
                (mrgSingle ((1, And (SSBool "a") (SSBool "b")), (-1, Or (SSBool "a") (SSBool "b")), (0, AndMonoidSBool $ And (SSBool "b") (SSBool "a"))))
                (mrgSingle ((1, Or (SSBool "a") (SSBool "b")), (-1, And (SSBool "a") (SSBool "b")), (0, AndMonoidSBool $ Or (SSBool "b") (SSBool "a"))))
        RWSTStrict.runRWST rws3 (0, SSBool "a") (1, SSBool "b") `shouldBe` res1
        RWSTStrict.runRWST rws3u1 (0, SSBool "a") (1, SSBool "b") `shouldBe` res1
    describe "SimpleMergeable for WriterT" $ do
      it "SimpleMergeable for lazy WriterT should work" $ do
        let st1 :: WriterLazy.WriterT (Monoid.Sum Integer) (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgSingle (SSBool "a", 1)
        let st2 :: WriterLazy.WriterT (Monoid.Sum Integer) (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgSingle (SSBool "b", 2)
        let st3 :: WriterLazy.WriterT (Monoid.Sum Integer) (UnionMBase SBool) SBool =
              WriterLazy.WriterT $ mrgSingle (SSBool "c", 1)
        let st4 = mrgIte (SSBool "d") st1 st2
        let st41 = mrgIte1 (SSBool "d") st1 st2
        let st4u1 = mrgIf (SSBool "d") st1 st2
        let st5 = mrgIte (SSBool "d") st1 st3
        let st51 = mrgIte1 (SSBool "d") st1 st3
        let st5u1 = mrgIf (SSBool "d") st1 st3
        WriterLazy.runWriterT st4 `shouldBe` mrgIf (SSBool "d") (mrgSingle (SSBool "a", 1)) (mrgSingle (SSBool "b", 2))
        WriterLazy.runWriterT st41 `shouldBe` mrgIf (SSBool "d") (mrgSingle (SSBool "a", 1)) (mrgSingle (SSBool "b", 2))
        WriterLazy.runWriterT st4u1 `shouldBe` mrgIf (SSBool "d") (mrgSingle (SSBool "a", 1)) (mrgSingle (SSBool "b", 2))
        WriterLazy.runWriterT st5 `shouldBe` mrgSingle (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterLazy.runWriterT st51 `shouldBe` mrgSingle (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterLazy.runWriterT st5u1 `shouldBe` mrgSingle (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
      it "SimpleMergeable for strict WriterT should work" $ do
        let st1 :: WriterStrict.WriterT (Monoid.Sum Integer) (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgSingle (SSBool "a", 1)
        let st2 :: WriterStrict.WriterT (Monoid.Sum Integer) (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgSingle (SSBool "b", 2)
        let st3 :: WriterStrict.WriterT (Monoid.Sum Integer) (UnionMBase SBool) SBool =
              WriterStrict.WriterT $ mrgSingle (SSBool "c", 1)
        let st4 = mrgIte (SSBool "d") st1 st2
        let st41 = mrgIte1 (SSBool "d") st1 st2
        let st4u1 = mrgIf (SSBool "d") st1 st2
        let st5 = mrgIte (SSBool "d") st1 st3
        let st51 = mrgIte1 (SSBool "d") st1 st3
        let st5u1 = mrgIf (SSBool "d") st1 st3
        WriterStrict.runWriterT st4 `shouldBe` mrgIf (SSBool "d") (mrgSingle (SSBool "a", 1)) (mrgSingle (SSBool "b", 2))
        WriterStrict.runWriterT st41 `shouldBe` mrgIf (SSBool "d") (mrgSingle (SSBool "a", 1)) (mrgSingle (SSBool "b", 2))
        WriterStrict.runWriterT st4u1 `shouldBe` mrgIf (SSBool "d") (mrgSingle (SSBool "a", 1)) (mrgSingle (SSBool "b", 2))
        WriterStrict.runWriterT st5 `shouldBe` mrgSingle (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterStrict.runWriterT st51 `shouldBe` mrgSingle (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
        WriterStrict.runWriterT st5u1 `shouldBe` mrgSingle (ITE (SSBool "d") (SSBool "a") (SSBool "c"), 1)
    describe "SimpleMergeable for ReaderT" $ do
      it "SimpleMergeable for ReaderT should work" $ do
        let r1 :: ReaderT Integer (UnionMBase SBool) Integer =
              ReaderT $ \(x :: Integer) -> mrgSingle $ x + 2
        let r2 :: ReaderT Integer (UnionMBase SBool) Integer =
              ReaderT $ \(x :: Integer) -> mrgSingle $ x * 2
        let r3 = mrgIte (SSBool "c") r1 r2
        -- let r31 = mrgIte1 (SSBool "c") r1 r2
        let r3u1 = mrgIf (SSBool "c") r1 r2
        runReaderT r3 2 `shouldBe` mrgSingle 4
        runReaderT r3 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle 5) (mrgSingle 6)
        -- runReaderT r31 2 `shouldBe` mrgSingle 4
        -- runReaderT r31 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle 5) (mrgSingle 6)
        runReaderT r3u1 2 `shouldBe` mrgSingle 4
        runReaderT r3u1 3 `shouldBe` mrgIf (SSBool "c") (mrgSingle 5) (mrgSingle 6)

        let r4 :: ReaderT SBool (UnionMBase SBool) SBool =
              ReaderT $ \x -> mrgSingle $ x &&~ (SSBool "x")
        let r5 :: ReaderT SBool (UnionMBase SBool) SBool =
              ReaderT $ \x -> mrgSingle $ x ||~ (SSBool "y")
        let r61 = mrgIte1 (SSBool "c") r4 r5
        runReaderT r61 (SSBool "a") `shouldBe` mrgSingle (ites (SSBool "c") (SSBool "a" &&~ SSBool "x") (SSBool "a" ||~ SSBool "y"))
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
        let i1 :: IdentityT (UnionMBase SBool) SBool = IdentityT $ mrgSingle $ SSBool "a"
        let i2 :: IdentityT (UnionMBase SBool) SBool = IdentityT $ mrgSingle $ SSBool "b"
        let i3 = mrgIte (SSBool "c") i1 i2
        let i31 = mrgIte1 (SSBool "c") i1 i2
        let i3u1 = mrgIf (SSBool "c") i1 i2
        runIdentityT i3 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
        runIdentityT i31 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
        runIdentityT i3u1 `shouldBe` mrgSingle (ITE (SSBool "c") (SSBool "a") (SSBool "b"))
