module Grisette.Control.Monad.UnionMBaseSpec where

import Control.Monad.Identity hiding (guard)
import qualified Data.HashMap.Strict as M
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.UnionOp
import Grisette.Data.UnionBase
import Test.Hspec
import Utils.SBool
import qualified Data.HashSet as S
import Grisette.Data.Class.ExtractSymbolics

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
  describe "SymEval for UnionMBase" $ do
    it "SymEval for UnionMBase should work" $ do
      let model = M.empty :: M.HashMap Symbol Bool
      let model1 =
            M.fromList
              [ (SSymbol "a", True),
                (SSymbol "b", False),
                (SSymbol "c", True)
              ] ::
              M.HashMap Symbol Bool
      symeval False model (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool)
      symeval True model (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ CBool False :: UnionMBase SBool SBool)
      symeval False model1 (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ CBool True :: UnionMBase SBool SBool)
      symeval True model1 (mrgReturn $ SSBool "a") `shouldBe` (mrgReturn $ CBool True :: UnionMBase SBool SBool)
      symeval False model1 (mrgIf (SSBool "a") (mrgReturn $ Left (SSBool "d")) (mrgReturn $ Right (SSBool "e")))
        `shouldBe` (mrgReturn $ Left $ SSBool "d" :: UnionMBase SBool (Either SBool SBool))
      symeval True model1 (mrgIf (SSBool "a") (mrgReturn $ Left (SSBool "d")) (mrgReturn $ Right (SSBool "e")))
        `shouldBe` (mrgReturn $ Left $ CBool False :: UnionMBase SBool (Either SBool SBool))
      symeval False model1 (mrgIf (SSBool "d") (mrgReturn $ Left (SSBool "a")) (mrgReturn $ Right (SSBool "b")))
        `shouldBe` ( mrgIf (SSBool "d") (mrgReturn $ Left $ CBool True) (mrgReturn $ Right $ CBool False) ::
                       UnionMBase SBool (Either SBool SBool)
                   )
      symeval True model1 (mrgIf (SSBool "d") (mrgReturn $ Left (SSBool "a")) (mrgReturn $ Right (SSBool "b")))
        `shouldBe` (mrgReturn $ Right $ CBool False :: UnionMBase SBool (Either SBool SBool))
      symeval False model1 (mrgIf (SSBool "a") (mrgReturn $ Left (SSBool "b")) (mrgReturn $ Right (SSBool "c")))
        `shouldBe` (mrgReturn $ Left $ CBool False :: UnionMBase SBool (Either SBool SBool))
  describe "ExtractSymbolics for UnionMBase" $ do
    it "ExtractSymbolic for UnionMBase should work" $ do
      extractSymbolics (mrgReturn $ SSBool "a" :: UnionMBase SBool SBool) `shouldBe`
        S.singleton (SSymbol "a")
      extractSymbolics (mrgIf (SSBool "a") (mrgReturn $ Left $ SSBool "b") (mrgReturn $ Right $ SSBool "c")
        :: UnionMBase SBool (Either SBool SBool)) `shouldBe`
        S.fromList [SSymbol "a", SSymbol "b", SSymbol "c"]
