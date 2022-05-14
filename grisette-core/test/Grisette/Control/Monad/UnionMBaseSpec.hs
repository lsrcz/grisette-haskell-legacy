{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Grisette.Control.Monad.UnionMBaseSpec where

import Control.Monad.Identity hiding (guard)
import qualified Data.ByteString as B
import qualified Data.HashMap.Lazy as ML
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Grisette.Control.Monad.Union
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Function
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.Evaluate
import Grisette.Data.Class.GenSym
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.UnionOp
import Grisette.Data.UnionBase
import Test.Hspec
import Utils.SBool

spec :: Spec
spec = do
  describe "Mergeable for UnionMBase" $ do
    it "Mergeable for UnionMBase should work" $ do
      let r =
            ( mrgIf
                (SSBool "a")
                (mrgReturn (mrgIf (SSBool "b") (mrgReturn $ Left $ SSBool "c") (mrgReturn $ Right $ SSBool "d")))
                (mrgReturn (mrgIf (SSBool "e") (mrgReturn $ Left $ SSBool "f") (mrgReturn $ Right $ SSBool "g"))) ::
                UnionMBase SBool (UnionMBase SBool (Either SBool SBool))
            )
      isMerged r `shouldBe` True
      underlyingUnion (underlyingUnion <$> r)
        `shouldBe` Single
          ( Guard
              (Left $ ITE (SSBool "a") (SSBool "c") (SSBool "f"))
              True
              (ITE (SSBool "a") (SSBool "b") (SSBool "e"))
              (Single $ Left $ ITE (SSBool "a") (SSBool "c") (SSBool "f"))
              (Single $ Right $ ITE (SSBool "a") (SSBool "d") (SSBool "g"))
          )
  describe "SimpleMergeable for UnionMBase" $ do
    it "SimpleMergeable for UnionMBase should work" $ do
      let l :: UnionMBase SBool (Either SBool SBool) = mrgIf (SSBool "b") (mrgReturn $ Left $ SSBool "c") (mrgReturn $ Right $ SSBool "d")
      let r = mrgIf (SSBool "e") (mrgReturn $ Left $ SSBool "f") (mrgReturn $ Right $ SSBool "g")
      let res = mrgIte (SSBool "a") l r
      let resu1 = mrgIteu1 (SSBool "a") l r
      let ref =
            Guard
              (Left $ ITE (SSBool "a") (SSBool "c") (SSBool "f"))
              True
              (ITE (SSBool "a") (SSBool "b") (SSBool "e"))
              (Single $ Left $ ITE (SSBool "a") (SSBool "c") (SSBool "f"))
              (Single $ Right $ ITE (SSBool "a") (SSBool "d") (SSBool "g"))
      isMerged res `shouldBe` True
      underlyingUnion res `shouldBe` ref
      isMerged resu1 `shouldBe` True
      underlyingUnion resu1 `shouldBe` ref
    it "SimpleMergeable1 for UnionMBase should work" $ do
      let l :: UnionMBase SBool SBool = mrgIf (SSBool "b") (mrgReturn $ SSBool "c") (mrgReturn $ SSBool "d")
      let r :: UnionMBase SBool SBool = mrgIf (SSBool "e") (mrgReturn $ SSBool "f") (mrgReturn $ SSBool "g")
      let res = mrgIte1 (SSBool "a") l r
      isMerged res `shouldBe` True
      underlyingUnion res
        `shouldBe` Single
          ( ITE
              (SSBool "a")
              (ITE (SSBool "b") (SSBool "c") (SSBool "d"))
              (ITE (SSBool "e") (SSBool "f") (SSBool "g"))
          )
  describe "Functor for UnionMBase" $ do
    it "fmap should work but would strip mergeable knowledge" $ do
      let x :: UnionMBase SBool Integer = (+ 1) <$> mrgIf (SSBool "a") (mrgReturn 1) (mrgReturn 2)
      x `shouldBe` guard (SSBool "a") (return 2) (return 3)
  describe "Applicative for UnionMBase" $ do
    it "pure should work but won't give us mergeable knowledge" $ do
      (pure 1 :: UnionMBase SBool Integer) `shouldBe` single 1
    it "<*> should work but won't give us mergeable knowledge" $ do
      let f :: UnionMBase SBool (Integer -> Integer) = mrgIf (SSBool "a") (mrgReturn id) (mrgReturn (+ 1))
      let v :: UnionMBase SBool Integer = mrgIf (SSBool "b") (mrgReturn 1) (mrgReturn 3)
      f <*> v
        `shouldBe` guard
          (SSBool "a")
          (guard (SSBool "b") (single 1) (single 3))
          (guard (SSBool "b") (single 2) (single 4))
  describe "Monad for UnionMBase" $ do
    it "return should work but won't give us mergeable knowledge" $ do
      (pure 1 :: UnionMBase SBool Integer) `shouldBe` single 1
    it ">>= should work and keeps mergeable knowledge" $ do
      let v :: UnionMBase SBool Integer = mrgIf (SSBool "a") (mrgReturn 0) (mrgReturn 1)
      let f :: Integer -> UnionMBase SBool Integer = \i -> mrgIf (SSBool "b") (mrgReturn $ i + 1) (mrgReturn $ i + 3)
      (v >>= f)
        `shouldBe` mrgIf
          (SSBool "a")
          (mrgIf (SSBool "b") (mrgReturn 1) (mrgReturn 3))
          (mrgIf (SSBool "b") (mrgReturn 2) (mrgReturn 4))
  describe "UnionOp for UnionMBase" $ do
    it "single for UnionMBase should work" $ do
      let r1 :: UnionMBase SBool SBool = single (SSBool "a")
      isMerged r1 `shouldBe` False
      underlyingUnion r1 `shouldBe` Single (SSBool "a")
    it "guard for UnionMBase should work when no merged" $ do
      let r1 :: UnionMBase SBool SBool = guard (SSBool "a") (single $ SSBool "b") (single $ SSBool "c")
      isMerged r1 `shouldBe` False
      underlyingUnion r1 `shouldBe` Guard (SSBool "b") False (SSBool "a") (Single $ SSBool "b") (Single $ SSBool "c")
    it "guard for UnionMBase should propagate and merge the results when some branch merged" $ do
      let r1 :: UnionMBase SBool SBool = guard (SSBool "a") (mrgReturn $ SSBool "b") (single $ SSBool "c")
      isMerged r1 `shouldBe` True
      underlyingUnion r1 `shouldBe` Single (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
      let r2 :: UnionMBase SBool SBool = guard (SSBool "a") (single $ SSBool "b") (mrgReturn $ SSBool "c")
      isMerged r2 `shouldBe` True
      underlyingUnion r2 `shouldBe` Single (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
      let r3 :: UnionMBase SBool SBool = guard (SSBool "a") (mrgReturn $ SSBool "b") (mrgReturn $ SSBool "c")
      isMerged r3 `shouldBe` True
      underlyingUnion r3 `shouldBe` Single (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    it "singleView for UnionMBase should work" $ do
      singleView (single $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe` Just (SSBool "a")
      singleView (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe` Just (SSBool "a")
      singleView
        ( guard (SSBool "a") (single $ Left $ SSBool "b") (single $ Right $ SSBool "c") ::
            UnionMBase SBool (Either SBool SBool)
        )
        `shouldBe` Nothing
      case (single $ SSBool "a" :: UnionMBase SBool SBool) of
        SingleU r -> r `shouldBe` SSBool "a"
        _ -> expectationFailure "SingleU match failed"
      case (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) of
        SingleU r -> r `shouldBe` SSBool "a"
        _ -> expectationFailure "SingleU match failed"
      case ( guard (SSBool "a") (single $ Left $ SSBool "b") (single $ Right $ SSBool "c") ::
               UnionMBase SBool (Either SBool SBool)
           ) of
        SingleU _ -> expectationFailure "SingleU match failed"
        _ -> return ()
    it "guardView for UnionMBase should work" $ do
      let r1 :: UnionMBase SBool (Either SBool SBool) =
            guard (SSBool "a") (single $ Left $ SSBool "b") (single $ Right $ SSBool "c")
      let r2 :: UnionMBase SBool (Either SBool SBool) =
            mrgIf (SSBool "a") (mrgReturn $ Left $ SSBool "b") (mrgReturn $ Right $ SSBool "c")
      guardView r1 `shouldBe` Just (SSBool "a", single $ Left $ SSBool "b", single $ Right $ SSBool "c")
      guardView r2 `shouldBe` Just (SSBool "a", mrgReturn $ Left $ SSBool "b", mrgReturn $ Right $ SSBool "c")
      guardView (single $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe` Nothing
      case r1 of
        GuardU c l r -> do
          c `shouldBe` SSBool "a"
          l `shouldBe` single (Left $ SSBool "b")
          r `shouldBe` single (Right $ SSBool "c")
        _ -> expectationFailure "SingleU match failed"
      case r2 of
        GuardU c l r -> do
          c `shouldBe` SSBool "a"
          l `shouldBe` mrgReturn (Left $ SSBool "b")
          r `shouldBe` mrgReturn (Right $ SSBool "c")
        _ -> expectationFailure "SingleU match failed"
      case single $ SSBool "a" :: UnionMBase SBool SBool of
        GuardU {} -> expectationFailure "SingleU match failed"
        _ -> return ()
    it "leftMost for UnionMBase should work" $ do
      leftMost (single $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe` SSBool "a"
      leftMost (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe` SSBool "a"
      let r1 :: UnionMBase SBool (Either SBool SBool) =
            guard (SSBool "a") (single $ Left $ SSBool "b") (single $ Right $ SSBool "c")
      let r2 :: UnionMBase SBool (Either SBool SBool) =
            mrgIf (SSBool "a") (mrgReturn $ Left $ SSBool "b") (mrgReturn $ Right $ SSBool "c")
      leftMost r1 `shouldBe` Left (SSBool "b")
      leftMost r2 `shouldBe` Left (SSBool "b")
  describe "MonadUnion for UnionMBase" $ do
    it "merge for UnionMBase should work" $ do
      let r1 :: UnionMBase SBool SBool = merge (guard (SSBool "a") (single $ SSBool "b") (single $ SSBool "c"))
      isMerged r1 `shouldBe` True
      underlyingUnion r1 `shouldBe` Single (ITE (SSBool "a") (SSBool "b") (SSBool "c"))
    it "mrgReturn for UnionMBase should work" $ do
      let r1 :: UnionMBase SBool SBool = mrgReturn (SSBool "a")
      isMerged r1 `shouldBe` True
      underlyingUnion r1 `shouldBe` Single (SSBool "a")
    describe "mrgIf for UnionMBase should work" $ do
      it "mrgIf should perform lazy evaluation" $ do
        (mrgIf (CBool True) (mrgReturn $ SSBool "a") undefined :: UnionMBase SBool SBool)
          `shouldBe` mrgReturn (SSBool "a")
        (mrgIf (CBool False) undefined (mrgReturn $ SSBool "a") :: UnionMBase SBool SBool)
          `shouldBe` mrgReturn (SSBool "a")
      it "mrgIf should work" $ do
        (mrgIf (SSBool "a") (single $ SSBool "b") (single $ SSBool "c") :: UnionMBase SBool SBool)
          `shouldBe` merge (guard (SSBool "a") (single $ SSBool "b") (single $ SSBool "c"))
  describe "SEq for UnionMBase" $ do
    it "SEq with Single/Single" $ do
      (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) ==~ mrgReturn (SSBool "b")
        `shouldBe` Equal (SSBool "a") (SSBool "b")
    let g1 :: UnionMBase SBool (Either SBool SBool) =
          mrgIf (SSBool "a") (mrgReturn $ Left $ SSBool "b") (mrgReturn $ Right $ SSBool "c")
    let g2 :: UnionMBase SBool (Either SBool SBool) =
          mrgIf (SSBool "d") (mrgReturn $ Left $ SSBool "e") (mrgReturn $ Right $ SSBool "f")
    it "SEq with Guard/Single" $ do
      g1 ==~ mrgReturn (Left $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (Equal (SSBool "b") (SSBool "d")) (CBool False)
      g1 ==~ mrgReturn (Right $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (CBool False) (Equal (SSBool "c") (SSBool "d"))
    it "SEq with Single/Guard" $ do
      mrgReturn (Left $ SSBool "d") ==~ g1
        `shouldBe` ITE (SSBool "a") (Equal (SSBool "d") (SSBool "b")) (CBool False)
      mrgReturn (Right $ SSBool "d") ==~ g1
        `shouldBe` ITE (SSBool "a") (CBool False) (Equal (SSBool "d") (SSBool "c"))
    it "SEq with Guard/Guard" $ do
      g1 ==~ g2
        `shouldBe` ITE
          (SSBool "a")
          (ITE (SSBool "d") (Equal (SSBool "b") (SSBool "e")) (CBool False))
          (ITE (SSBool "d") (CBool False) (Equal (SSBool "c") (SSBool "f")))
  describe "SOrd for UnionMBase" $ do
    it "SOrd with Single/Single" $ do
      (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) <=~ mrgReturn (SSBool "b")
        `shouldBe` (SSBool "a" <=~ SSBool "b" :: SBool)
      (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) <~ mrgReturn (SSBool "b")
        `shouldBe` (SSBool "a" <~ SSBool "b" :: SBool)
      (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) >=~ mrgReturn (SSBool "b")
        `shouldBe` (SSBool "a" >=~ SSBool "b" :: SBool)
      (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) >~ mrgReturn (SSBool "b")
        `shouldBe` (SSBool "a" >~ SSBool "b" :: SBool)
      (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) `symCompare` mrgReturn (SSBool "b")
        `shouldBe` (SSBool "a" `symCompare` SSBool "b" :: UnionMBase SBool Ordering)
    let g1 :: UnionMBase SBool (Either SBool SBool) =
          mrgIf (SSBool "a") (mrgReturn $ Left $ SSBool "b") (mrgReturn $ Right $ SSBool "c")
    let g2 :: UnionMBase SBool (Either SBool SBool) =
          mrgIf (SSBool "d") (mrgReturn $ Left $ SSBool "e") (mrgReturn $ Right $ SSBool "f")
    it "SOrd with Guard/Single" $ do
      g1 <=~ mrgReturn (Left $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (SSBool "b" <=~ SSBool "d") (CBool False)
      g1 <~ mrgReturn (Left $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (SSBool "b" <~ SSBool "d") (CBool False)
      g1 >=~ mrgReturn (Left $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (SSBool "b" >=~ SSBool "d") (CBool True)
      g1 >~ mrgReturn (Left $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (SSBool "b" >~ SSBool "d") (CBool True)

      g1 `symCompare` mrgReturn (Left $ SSBool "d")
        `shouldBe` ( mrgIf (SSBool "a") (SSBool "b" `symCompare` SSBool "d") (mrgReturn GT) ::
                       UnionMBase SBool Ordering
                   )

      g1 <=~ mrgReturn (Right $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (CBool True) (SSBool "c" <=~ SSBool "d")
      g1 <~ mrgReturn (Right $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (CBool True) (SSBool "c" <~ SSBool "d")
      g1 >=~ mrgReturn (Right $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (CBool False) (SSBool "c" >=~ SSBool "d")
      g1 >~ mrgReturn (Right $ SSBool "d")
        `shouldBe` ITE (SSBool "a") (CBool False) (SSBool "c" >~ SSBool "d")

      g1 `symCompare` mrgReturn (Right $ SSBool "d")
        `shouldBe` ( mrgIf (SSBool "a") (mrgReturn LT) (SSBool "c" `symCompare` SSBool "d") ::
                       UnionMBase SBool Ordering
                   )
    it "SOrd with Single/Guard" $ do
      mrgReturn (Left $ SSBool "d") <=~ g1
        `shouldBe` ITE (SSBool "a") (SSBool "d" <=~ SSBool "b") (CBool True)
      mrgReturn (Left $ SSBool "d") <~ g1
        `shouldBe` ITE (SSBool "a") (SSBool "d" <~ SSBool "b") (CBool True)
      mrgReturn (Left $ SSBool "d") >=~ g1
        `shouldBe` ITE (SSBool "a") (SSBool "d" >=~ SSBool "b") (CBool False)
      mrgReturn (Left $ SSBool "d") >~ g1
        `shouldBe` ITE (SSBool "a") (SSBool "d" >~ SSBool "b") (CBool False)

      mrgReturn (Left $ SSBool "d") `symCompare` g1
        `shouldBe` ( mrgIf (SSBool "a") (SSBool "d" `symCompare` SSBool "b") (mrgReturn LT) ::
                       UnionMBase SBool Ordering
                   )

      mrgReturn (Right $ SSBool "d") <=~ g1
        `shouldBe` ITE (SSBool "a") (CBool False) (SSBool "d" <=~ SSBool "c")
      mrgReturn (Right $ SSBool "d") <~ g1
        `shouldBe` ITE (SSBool "a") (CBool False) (SSBool "d" <~ SSBool "c")
      mrgReturn (Right $ SSBool "d") >=~ g1
        `shouldBe` ITE (SSBool "a") (CBool True) (SSBool "d" >=~ SSBool "c")
      mrgReturn (Right $ SSBool "d") >~ g1
        `shouldBe` ITE (SSBool "a") (CBool True) (SSBool "d" >~ SSBool "c")

      mrgReturn (Right $ SSBool "d") `symCompare` g1
        `shouldBe` ( mrgIf (SSBool "a") (mrgReturn GT) (SSBool "d" `symCompare` SSBool "c") ::
                       UnionMBase SBool Ordering
                   )
    it "SOrd with Guard/Guard" $ do
      g1 <=~ g2
        `shouldBe` ITE
          (SSBool "a")
          (ITE (SSBool "d") (SSBool "b" <=~ SSBool "e") (CBool True))
          (ITE (SSBool "d") (CBool False) (SSBool "c" <=~ SSBool "f"))
      g1 <~ g2
        `shouldBe` ITE
          (SSBool "a")
          (ITE (SSBool "d") (SSBool "b" <~ SSBool "e") (CBool True))
          (ITE (SSBool "d") (CBool False) (SSBool "c" <~ SSBool "f"))
      g1 >=~ g2
        `shouldBe` ITE
          (SSBool "a")
          (ITE (SSBool "d") (SSBool "b" >=~ SSBool "e") (CBool False))
          (ITE (SSBool "d") (CBool True) (SSBool "c" >=~ SSBool "f"))
      g1 >~ g2
        `shouldBe` ITE
          (SSBool "a")
          (ITE (SSBool "d") (SSBool "b" >~ SSBool "e") (CBool False))
          (ITE (SSBool "d") (CBool True) (SSBool "c" >~ SSBool "f"))
      g1 `symCompare` g2
        `shouldBe` ( mrgIf
                       (SSBool "a")
                       (mrgIf (SSBool "d") (SSBool "b" `symCompare` SSBool "e") (mrgReturn LT))
                       (mrgIf (SSBool "d") (mrgReturn GT) (SSBool "c" `symCompare` SSBool "f")) ::
                       UnionMBase SBool Ordering
                   )
  describe "ToSym for UnionMBase" $ do
    it "ToSym from single" $ do
      (toSym True :: UnionMBase SBool SBool) `shouldBe` mrgReturn (CBool True)
    it "ToSym from UnionMBase" $ do
      (toSym (mrgReturn True :: UnionMBase SBool Bool) :: UnionMBase SBool SBool) `shouldBe` mrgReturn (CBool True)
    it "ToSym from Identity" $ do
      (toSym (Identity True :: Identity Bool) :: UnionMBase SBool SBool) `shouldBe` mrgReturn (CBool True)
  describe "ToCon for UnionMBase" $ do
    it "ToCon for UnionMBase should work" $ do
      (toCon (mrgReturn (CBool True) :: UnionMBase SBool SBool) :: Maybe Bool) `shouldBe` Just True
      (toCon (mrgReturn (SSBool "a") :: UnionMBase SBool SBool) :: Maybe Bool) `shouldBe` Nothing
      ( toCon (mrgIf (SSBool "a") (mrgReturn (1 :: Integer)) (mrgReturn (2 :: Integer)) :: UnionMBase SBool Integer) ::
          Maybe Integer
        )
        `shouldBe` Nothing
  describe "Evaluate for UnionMBase" $ do
    it "Evaluate for UnionMBase should work" $ do
      let model = M.empty :: M.HashMap Symbol Bool
      let model1 =
            M.fromList
              [ (SSymbol "a", True),
                (SSymbol "b", False),
                (SSymbol "c", True)
              ] ::
              M.HashMap Symbol Bool
      evaluate False model (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool)
      evaluate True model (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ CBool False :: UnionMBase SBool SBool)
      evaluate False model1 (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ CBool True :: UnionMBase SBool SBool)
      evaluate True model1 (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ CBool True :: UnionMBase SBool SBool)
      evaluate False model1 (mrgIf (SSBool "a") (mrgReturn $ Left (SSBool "d")) (mrgReturn $ Right (SSBool "e")))
        `shouldBe` (mrgReturn $ Left $ SSBool "d" :: UnionMBase SBool (Either SBool SBool))
      evaluate True model1 (mrgIf (SSBool "a") (mrgReturn $ Left (SSBool "d")) (mrgReturn $ Right (SSBool "e")))
        `shouldBe` (mrgReturn $ Left $ CBool False :: UnionMBase SBool (Either SBool SBool))
      evaluate False model1 (mrgIf (SSBool "d") (mrgReturn $ Left (SSBool "a")) (mrgReturn $ Right (SSBool "b")))
        `shouldBe` ( mrgIf (SSBool "d") (mrgReturn $ Left $ CBool True) (mrgReturn $ Right $ CBool False) ::
                       UnionMBase SBool (Either SBool SBool)
                   )
      evaluate True model1 (mrgIf (SSBool "d") (mrgReturn $ Left (SSBool "a")) (mrgReturn $ Right (SSBool "b")))
        `shouldBe` (mrgReturn $ Right $ CBool False :: UnionMBase SBool (Either SBool SBool))
      evaluate False model1 (mrgIf (SSBool "a") (mrgReturn $ Left (SSBool "b")) (mrgReturn $ Right (SSBool "c")))
        `shouldBe` (mrgReturn $ Left $ CBool False :: UnionMBase SBool (Either SBool SBool))
  describe "ExtractSymbolics for UnionMBase" $ do
    it "ExtractSymbolic for UnionMBase should work" $ do
      extractSymbolics (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool)
        `shouldBe` S.singleton (SSymbol "a")
      extractSymbolics
        ( mrgIf (SSBool "a") (mrgReturn $ Left $ SSBool "b") (mrgReturn $ Right $ SSBool "c") ::
            UnionMBase SBool (Either SBool SBool)
        )
        `shouldBe` S.fromList [SSymbol "a", SSymbol "b", SSymbol "c"]
  describe "Num for UnionMBase" $ do
    describe "Num for UnionMBase should work" $ do
      it "fromInteger for UnionMBase should work" $ do
        (1 :: UnionMBase SBool Integer) `shouldBe` mrgReturn 1
      it "negate for UnionMBase should work" $ do
        negate (mrgIf (SSBool "a") (mrgReturn 1) (mrgReturn 2) :: UnionMBase SBool Integer)
          `shouldBe` mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn $ -2)
      it "plus for UnionMBase should work" $ do
        (mrgIf (SSBool "a") (mrgReturn 0) (mrgReturn 1) :: UnionMBase SBool Integer)
          + mrgIf (SSBool "b") (mrgReturn 1) (mrgReturn 3)
          `shouldBe` mrgIf
            (SSBool "a")
            (mrgIf (SSBool "b") (mrgReturn 1) (mrgReturn 3))
            (mrgIf (SSBool "b") (mrgReturn 2) (mrgReturn 4))
      it "minus for UnionMBase should work" $ do
        (mrgIf (SSBool "a") (mrgReturn 0) (mrgReturn 1) :: UnionMBase SBool Integer)
          - mrgIf (SSBool "b") (mrgReturn $ -3) (mrgReturn $ -1)
          `shouldBe` mrgIf
            (SSBool "a")
            (mrgIf (Not $ SSBool "b") (mrgReturn 1) (mrgReturn 3))
            (mrgIf (Not $ SSBool "b") (mrgReturn 2) (mrgReturn 4))
      it "times for UnionMBase should work" $ do
        (mrgIf (SSBool "a") (mrgReturn 1) (mrgReturn 2) :: UnionMBase SBool Integer)
          * mrgIf (SSBool "b") (mrgReturn 3) (mrgReturn 4)
          `shouldBe` mrgIf
            (SSBool "a")
            (mrgIf (SSBool "b") (mrgReturn 3) (mrgReturn 4))
            (mrgIf (SSBool "b") (mrgReturn 6) (mrgReturn 8))
      it "abs for UnionMBase should work" $ do
        abs (mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn 2) :: UnionMBase SBool Integer)
          `shouldBe` mrgIf (SSBool "a") (mrgReturn $ 1) (mrgReturn $ 2)
      it "signum for UnionMBase should work" $ do
        signum (mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn 2) :: UnionMBase SBool Integer)
          `shouldBe` mrgIf (SSBool "a") (mrgReturn $ -1) (mrgReturn 1)
  describe "ITEOp for UnionMBase" $ do
    it "ites for UnionMBase should work" $ do
      ites (SSBool "a") (mrgReturn $ SSBool "b") (mrgReturn $ SSBool "c")
        `shouldBe` (mrgReturn (ITE (SSBool "a") (SSBool "b") (SSBool "c")) :: UnionMBase SBool SBool)
  describe "LogicalOp for UnionMBase" $ do
    let l = mrgIf (SSBool "a") (mrgReturn False) (mrgReturn True)
    let r = mrgIf (SSBool "b") (mrgReturn False) (mrgReturn True)
    it "||~ for UnionMBase should work" $ do
      l ||~ r `shouldBe` (mrgIf (And (SSBool "a") (SSBool "b")) (mrgReturn False) (mrgReturn True) :: UnionMBase SBool Bool)
    it "&&~ for UnionMBase should work" $ do
      l &&~ r `shouldBe` (mrgIf (Or (SSBool "a") (SSBool "b")) (mrgReturn False) (mrgReturn True) :: UnionMBase SBool Bool)
    it "nots for UnionMBase should work" $ do
      nots l `shouldBe` mrgIf (Not $ SSBool "a") (mrgReturn False) (mrgReturn True)
    it "xors for UnionMBase should work" $ do
      l `xors` r
        `shouldBe` ( mrgIf
                       (ITE (SSBool "a") (SSBool "b") (Not $ SSBool "b"))
                       (mrgReturn False)
                       (mrgReturn True) ::
                       UnionMBase SBool Bool
                   )
    it "implies for UnionMBase should work" $ do
      l `implies` r
        `shouldBe` ( mrgIf
                       (And (Not $ SSBool "a") (SSBool "b"))
                       (mrgReturn False)
                       (mrgReturn True) ::
                       UnionMBase SBool Bool
                   )
  describe "PrimWrapper for UnionMBase" $ do
    it "PrimWrapper should work for UnionMBase" $ do
      conc True `shouldBe` (mrgReturn $ CBool True :: UnionMBase SBool SBool)
      ssymb "a" `shouldBe` (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool)
      isymb 0 "a" `shouldBe` (mrgReturn $ ISBool 0 "a" :: UnionMBase SBool SBool)
      concView (mrgReturn $ CBool True :: UnionMBase SBool SBool) `shouldBe` Just True
      concView (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe` Nothing
      concView
        ( mrgIf
            (SSBool "a")
            (mrgReturn $ CBool False)
            (mrgReturn $ CBool True) ::
            UnionMBase SBool SBool
        )
        `shouldBe` Nothing
  describe "Function class for UnionMBase" $ do
    it "Applying function in UnionMBase" $ do
      let func = mrgIf (SSBool "a") (mrgReturn (+ 1)) (mrgReturn (+ 2)) :: UnionMBase SBool (Integer -> Integer)
      func # (1 :: Integer) `shouldBe` mrgIf (SSBool "a") (mrgReturn 2) (mrgReturn 3)
    it "Helper for applying on UnionMBase" $ do
      let func (x :: Integer) = mrgIf (SSBool "a") (mrgReturn $ x + 1) (mrgReturn $ x + 3)
      (func #~ mrgIf (SSBool "b") (mrgReturn 0) (mrgReturn 1))
        `shouldBe` ( mrgIf
                       (SSBool "b")
                       (mrgIf (SSBool "a") (mrgReturn 1) (mrgReturn 3))
                       (mrgIf (SSBool "a") (mrgReturn 2) (mrgReturn 4)) ::
                       UnionMBase SBool Integer
                   )
  describe "IsString for UnionMBase" $ do
    it "IsString for UnionMBase should work" $ do
      ("x" :: UnionMBase SBool B.ByteString) `shouldBe` mrgReturn "x"
  describe "GenSym for UnionMBase" $ do
    it "GenSym for UnionMBase with spec" $ do
      (genSym (ListSpec 1 3 ()) "a" :: UnionMBase SBool (UnionMBase SBool [SBool]))
        `shouldBe` mrgReturn
          ( mrgIf
              (ISBool 3 "a")
              (mrgReturn [ISBool 2 "a"])
              ( mrgIf
                  (ISBool 4 "a")
                  (mrgReturn [ISBool 1 "a", ISBool 2 "a"])
                  (mrgReturn [ISBool 0 "a", ISBool 1 "a", ISBool 2 "a"])
              )
          )
      (genSymSimple @SBool (ListSpec 1 3 ()) "a" :: UnionMBase SBool [SBool])
        `shouldBe` mrgIf
          (ISBool 3 "a")
          (mrgReturn [ISBool 2 "a"])
          ( mrgIf
              (ISBool 4 "a")
              (mrgReturn [ISBool 1 "a", ISBool 2 "a"])
              (mrgReturn [ISBool 0 "a", ISBool 1 "a", ISBool 2 "a"])
          )
    it "GenSym for UnionMBase with same shape" $ do
      ( genSym
          ( mrgIf
              (SSBool "a")
              (mrgReturn [SSBool "x"])
              (mrgReturn [SSBool "y", SSBool "z"]) ::
              UnionMBase SBool [SBool]
          )
          "a" ::
          UnionMBase SBool [SBool]
        )
        `shouldBe` mrgIf (ISBool 0 "a") (mrgReturn [ISBool 1 "a"]) (mrgReturn [ISBool 2 "a", ISBool 3 "a"])
  describe "Concrete Key HashMaps" $ do
    it "Concrete Key HashMap should work" $ do
      mrgIte
        (SSBool "a")
        ( ML.fromList [(1, mrgReturn $ Just 1), (2, mrgReturn $ Just 2)] ::
            ML.HashMap Integer (UnionMBase SBool (Maybe Integer))
        )
        (ML.fromList [(1, mrgReturn $ Just 2), (3, mrgReturn $ Just 3)])
        `shouldBe` ML.fromList
          [ (1, mrgIf (SSBool "a") (mrgReturn $ Just 1) (mrgReturn $ Just 2)),
            (2, mrgIf (Not $ SSBool "a") (mrgReturn Nothing) (mrgReturn $ Just 2)),
            (3, mrgIf (SSBool "a") (mrgReturn Nothing) (mrgReturn $ Just 3))
          ]
      mrgIf
        (SSBool "a")
        ( mrgReturn $ ML.fromList [(1, mrgReturn $ Just 1), (2, mrgReturn $ Just 2)] ::
            UnionMBase SBool (ML.HashMap Integer (UnionMBase SBool (Maybe Integer)))
        )
        (mrgReturn (ML.fromList [(1, mrgReturn $ Just 2), (3, mrgReturn $ Just 3)]))
        `shouldBe` mrgReturn
          ( ML.fromList
              [ (1, mrgIf (SSBool "a") (mrgReturn $ Just 1) (mrgReturn $ Just 2)),
                (2, mrgIf (Not $ SSBool "a") (mrgReturn Nothing) (mrgReturn $ Just 2)),
                (3, mrgIf (SSBool "a") (mrgReturn Nothing) (mrgReturn $ Just 3))
              ]
          )
