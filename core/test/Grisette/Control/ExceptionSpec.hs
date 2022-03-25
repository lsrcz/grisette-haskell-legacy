module Grisette.Control.ExceptionSpec where

import qualified Data.HashSet as S
import Grisette.Control.Exception
import Grisette.Control.Monad
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Test.Hspec
import Utils.SBool
import Grisette.Data.Class.Error
import Control.Exception
import Control.Monad.Except

spec :: Spec
spec = do
  describe "AssertionError" $ do
    it "ToCon for AssertionError" $ do
      toCon AssertionError `shouldBe` Just AssertionError
    it "ToSym for AssertionError" $ do
      toSym AssertionError `shouldBe` AssertionError
    it "SEq for AssertionError" $ do
      AssertionError ==~ AssertionError `shouldBe` CBool True
    it "SOrd for AssertionError" $ do
      AssertionError <=~ AssertionError `shouldBe` CBool True
      AssertionError <~ AssertionError `shouldBe` CBool False
      AssertionError >=~ AssertionError `shouldBe` CBool True
      AssertionError >~ AssertionError `shouldBe` CBool False
      AssertionError `symCompare` AssertionError `shouldBe` (mrgReturn EQ :: UnionMBase SBool Ordering)
    it "SymEval for AssertionError" $ do
      symeval False () AssertionError `shouldBe` AssertionError
    it "ExtractSymbolics for AssertionError" $ do
      extractSymbolics AssertionError `shouldBe` (S.empty :: S.HashSet Symbol)
    it "SimpleMergeable for AssertionError" $ do
      mrgIte (SSBool "a") AssertionError AssertionError `shouldBe` AssertionError
    it "Mergeable for AssertionError" $ do
      let SimpleStrategy s = mergeStrategy :: MergeStrategy SBool AssertionError
      s (SSBool "a") AssertionError AssertionError `shouldBe` AssertionError
    it "Transform AssertionError to VerificationConditions" $ do
      transformError AssertionError `shouldBe` AssertionViolation
    it "Transform AssertionError to AssertionError" $ do
      transformError AssertionError `shouldBe` AssertionError
    it "Transform ArrayException to AssertionError" $ do
      transformError (IndexOutOfBounds "") `shouldBe` AssertionError
    it "Transform ArrayException to AssertionError" $ do
      transformError (UndefinedElement "") `shouldBe` AssertionError
  describe "VerificationConditions" $ do
    it "ToCon for VerificationConditions" $ do
      toCon AssertionViolation `shouldBe` Just AssertionViolation
      toCon AssumptionViolation `shouldBe` Just AssumptionViolation
    it "ToSym for AssertionError" $ do
      toSym AssertionViolation `shouldBe` AssertionViolation
      toSym AssumptionViolation `shouldBe` AssumptionViolation
    it "SEq for AssertionError" $ do
      AssertionViolation ==~ AssertionViolation `shouldBe` CBool True
      AssertionViolation ==~ AssumptionViolation `shouldBe` CBool False
      AssumptionViolation ==~ AssertionViolation `shouldBe` CBool False
      AssumptionViolation ==~ AssumptionViolation `shouldBe` CBool True
    it "SOrd for AssertionError" $ do
      AssertionViolation <=~ AssertionViolation `shouldBe` CBool True
      AssertionViolation <~ AssertionViolation `shouldBe` CBool False
      AssertionViolation >=~ AssertionViolation `shouldBe` CBool True
      AssertionViolation >~ AssertionViolation `shouldBe` CBool False
      AssertionViolation `symCompare` AssertionViolation `shouldBe` (mrgReturn EQ :: UnionMBase SBool Ordering)

      AssertionViolation <=~ AssumptionViolation `shouldBe` CBool True
      AssertionViolation <~ AssumptionViolation `shouldBe` CBool True
      AssertionViolation >=~ AssumptionViolation `shouldBe` CBool False
      AssertionViolation >~ AssumptionViolation `shouldBe` CBool False
      AssertionViolation `symCompare` AssumptionViolation `shouldBe` (mrgReturn LT :: UnionMBase SBool Ordering)

      AssumptionViolation <=~ AssertionViolation `shouldBe` CBool False
      AssumptionViolation <~ AssertionViolation `shouldBe` CBool False
      AssumptionViolation >=~ AssertionViolation `shouldBe` CBool True
      AssumptionViolation >~ AssertionViolation `shouldBe` CBool True
      AssumptionViolation `symCompare` AssertionViolation `shouldBe` (mrgReturn GT :: UnionMBase SBool Ordering)

      AssumptionViolation <=~ AssumptionViolation `shouldBe` CBool True
      AssumptionViolation <~ AssumptionViolation `shouldBe` CBool False
      AssumptionViolation >=~ AssumptionViolation `shouldBe` CBool True
      AssumptionViolation >~ AssumptionViolation `shouldBe` CBool False
      AssumptionViolation `symCompare` AssumptionViolation `shouldBe` (mrgReturn EQ :: UnionMBase SBool Ordering)
    it "SymEval for VerificationConditions" $ do
      symeval False () AssertionViolation `shouldBe` AssertionViolation
      symeval False () AssumptionViolation `shouldBe` AssumptionViolation
    it "ExtractSymbolics for AssertionError" $ do
      extractSymbolics AssertionViolation `shouldBe` (S.empty :: S.HashSet Symbol)
      extractSymbolics AssumptionViolation `shouldBe` (S.empty :: S.HashSet Symbol)
    it "Mergeable for AssertionError" $ do
      mrgIf (SSBool "a") (mrgReturn AssumptionViolation) (mrgReturn AssertionViolation)
        `shouldBe` ( mrgIf (Not $ SSBool "a") (mrgReturn AssertionViolation) (mrgReturn AssumptionViolation) ::
                       UnionMBase SBool VerificationConditions
                   )
    it "Transform VerificationConditions to VerificationConditions" $ do
      transformError AssertionViolation `shouldBe` AssertionViolation
      transformError AssumptionViolation `shouldBe` AssumptionViolation
  describe "gassert" $ do
    it "gassert should work" $ do
      (gassert (SSBool "a") :: ExceptT VerificationConditions (UnionMBase SBool) ())
        `shouldBe` ExceptT (mrgIf (Not $ SSBool "a") (mrgReturn $ Left AssertionViolation) (mrgReturn $ Right ()))
    