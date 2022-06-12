{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Grisette.Data.SymPrimSpec where

import Control.Monad.Except
import qualified Data.BitVector.Sized.Signed as BVS
import qualified Data.BitVector.Sized.Unsigned as BVU
import Data.Bits
import qualified Data.HashSet as S
import Data.Proxy
import Grisette.Control.Monad.UnionM
import Grisette.Core.Data.Class.BitVector
import Grisette.Core.Data.Class.Bool
import Grisette.Core.Data.Class.ExtractSymbolics
import Grisette.Core.Data.Class.Integer
import Grisette.Core.Data.Class.Mergeable
import Grisette.Core.Data.Class.PrimWrapper
import Grisette.Core.Data.Class.SOrd
import Grisette.Core.Data.Class.SimpleMergeable
import Grisette.Core.Data.Class.Evaluate
import Grisette.Core.Data.Class.GenSym
import Grisette.Core.Data.Class.ToCon
import Grisette.Core.Data.Class.ToSym
import Grisette.Data.Prim.BV
import Grisette.Data.Prim.Bits
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Integer
import Grisette.Data.Prim.InternedTerm
import qualified Grisette.Data.Prim.Model as Model
import Grisette.Data.Prim.Num
import Grisette.Data.SymPrim
import Test.Hspec
import Test.Hspec.QuickCheck
import Grisette.Core.Data.Class.Function
import Grisette.Data.Prim.TabularFunc
import Grisette.Data.TabularFunc
import Data.Int
import Data.Word

spec :: Spec
spec = do
  describe "PrimWrapper for SymPrim" $ do
    it "conc should work" $ do
      (conc 1 :: Sym Integer) `shouldBe` Sym (concTerm 1)
    it "ssymb should work" $ do
      (ssymb "a" :: Sym Integer) `shouldBe` Sym (ssymbTerm "a")
    it "isymb should work" $ do
      (isymb 1 "a" :: Sym Integer) `shouldBe` Sym (isymbTerm 1 "a")
    it "concView should work" $ do
      concView (conc 1 :: Sym Integer) `shouldBe` Just 1
      concView (ssymb "a" :: Sym Integer) `shouldBe` Nothing
      case conc 1 :: Sym Integer of
        Conc 1 -> return ()
        _ -> expectationFailure "Bad match"
      case ssymb "a" :: Sym Integer of
        Conc _ -> expectationFailure "Bad match"
        _ -> return ()
  describe "ITEOp for SymPrim" $ do
    it "ites should work" $
      ites (ssymb "a" :: Sym Bool) (ssymb "b" :: Sym Integer) (ssymb "c")
        `shouldBe` Sym (iteterm (ssymbTerm "a") (ssymbTerm "b") (ssymbTerm "c"))
  describe "Mergeable for SymPrim" $ do
    it "Mergeable should work" $ do
      let SimpleStrategy s = mergeStrategy :: MergeStrategy (Sym Bool) (Sym Integer)
      s (ssymb "a") (ssymb "b") (ssymb "c")
        `shouldBe` ites (ssymb "a" :: Sym Bool) (ssymb "b" :: Sym Integer) (ssymb "c")
  describe "SimpleMergeable for SymPrim" $ do
    it "Mergeable should work" $ do
      mrgIte (ssymb "a" :: Sym Bool) (ssymb "b") (ssymb "c")
        `shouldBe` ites (ssymb "a" :: Sym Bool) (ssymb "b" :: Sym Integer) (ssymb "c")
  describe "IsString for SymPrim" $ do
    it "string literal should work" $ do
      ("a" :: Sym Bool) `shouldBe` Sym (ssymbTerm "a")
  describe "ToSym for SymPrim" $ do
    it "ToSym from self" $ do
      toSym (ssymb "a" :: Sym Bool) `shouldBe` (ssymb "a" :: Sym Bool)
    it "ToSym from concrete" $ do
      toSym True `shouldBe` (conc True :: Sym Bool)
  describe "ToCon for SymPrim" $ do
    it "ToCon to self" $ do
      toCon (ssymb "a" :: Sym Bool) `shouldBe` (Nothing :: Maybe Bool)
    it "ToCon to concrete" $ do
      toCon True `shouldBe` Just True
  describe "Evaluate for SymPrim" $ do
    it "evaluate for SymPrim should work" $ do
      let m1 = Model.empty
      let m2 = Model.insert m1 (TermSymbol (Proxy @Integer) (SimpleSymbol "a")) (1 :: Integer)
      let m3 = Model.insert m2 (TermSymbol (Proxy @Bool) (SimpleSymbol "b")) True
      evaluate False m3 (ites ("c" :: Sym Bool) "a" ("a" + "a" :: Sym Integer))
        `shouldBe` ites ("c" :: Sym Bool) 1 2
      evaluate True m3 (ites ("c" :: Sym Bool) "a" ("a" + "a" :: Sym Integer)) `shouldBe` 2
  describe "ExtractSymbolics" $ do
    it "extractSymbolics for SymPrim should work" $ do
      extractSymbolics (ites ("c" :: Sym Bool) ("a" :: Sym Integer) ("b" :: Sym Integer))
        `shouldBe` S.fromList
          [ TermSymbol (Proxy @Bool) (SimpleSymbol "c"),
            TermSymbol (Proxy @Integer) (SimpleSymbol "a"),
            TermSymbol (Proxy @Integer) (SimpleSymbol "b")
          ]
  describe "GenSym" $ do
    it "GenSym for SymPrim should work" $ do
      (genSym () "a" :: UnionM (Sym Bool)) `shouldBe` mrgSingle (isymb 0 "a")
      (genSymSimple @SymBool () "a" :: Sym Bool) `shouldBe` isymb 0 "a"
      (genSym (ssymb "a" :: Sym Bool) "a" :: UnionM (Sym Bool)) `shouldBe` mrgSingle (isymb 0 "a")
      (genSymSimple @SymBool (ssymb "a" :: Sym Bool) "a" :: Sym Bool) `shouldBe` isymb 0 "a"
      (genSym () (nameWithInfo "a" True) :: UnionM (Sym Bool)) `shouldBe` mrgSingle (iinfosymb 0 "a" True)
      (genSymSimple @SymBool () (nameWithInfo "a" True) :: Sym Bool) `shouldBe` iinfosymb 0 "a" True
  describe "SEq" $ do
    it "SEq for SymPrim should work" $ do
      (ssymb "a" :: Sym Bool) ==~ ssymb "b" `shouldBe` Sym (eqterm (ssymbTerm "a" :: Term Bool) (ssymbTerm "b"))
      (ssymb "a" :: Sym Bool) /=~ ssymb "b" `shouldBe` Sym (notb $ eqterm (ssymbTerm "a" :: Term Bool) (ssymbTerm "b"))
  describe "Sym Bool" $ do
    describe "LogicalOp for Sym Bool" $ do
      it "||~ for SymPrim should work" $ do
        ssymb "a" ||~ ssymb "b" `shouldBe` Sym (orb (ssymbTerm "a") (ssymbTerm "b"))
      it "&&~ for SymPrim should work" $ do
        ssymb "a" &&~ ssymb "b" `shouldBe` Sym (andb (ssymbTerm "a") (ssymbTerm "b"))
      it "nots for SymPrim should work" $ do
        nots (ssymb "a") `shouldBe` Sym (notb (ssymbTerm "a"))
      it "xors for SymPrim should work" $ do
        xors (ssymb "a") (ssymb "b") `shouldBe` Sym (xorb (ssymbTerm "a") (ssymbTerm "b"))
      it "implies for SymPrim should work" $ do
        implies (ssymb "a") (ssymb "b") `shouldBe` Sym (implyb (ssymbTerm "a") (ssymbTerm "b"))
  describe "Sym Integer" $ do
    describe "Num for Sym Integer" $ do
      it "fromInteger should work" $ do
        (1 :: Sym Integer) `shouldBe` Sym (concTerm 1)
      it "(+) for SymPrim should work" $ do
        (ssymb "a" :: Sym Integer) + ssymb "b" `shouldBe` Sym (addNum (ssymbTerm "a") (ssymbTerm "b"))
      it "(-) for SymPrim should work" $ do
        (ssymb "a" :: Sym Integer) - ssymb "b" `shouldBe` Sym (minusNum (ssymbTerm "a") (ssymbTerm "b"))
      it "(*) for SymPrim should work" $ do
        (ssymb "a" :: Sym Integer) * ssymb "b" `shouldBe` Sym (timesNum (ssymbTerm "a") (ssymbTerm "b"))
      it "negate for SymPrim should work" $ do
        negate (ssymb "a" :: Sym Integer) `shouldBe` Sym (uminusNum (ssymbTerm "a"))
      it "abs for SymPrim should work" $ do
        abs (ssymb "a" :: Sym Integer) `shouldBe` Sym (absNum (ssymbTerm "a"))
      it "signum for SymPrim should work" $ do
        signum (ssymb "a" :: Sym Integer) `shouldBe` Sym (signumNum (ssymbTerm "a"))
    describe "SignedDivMod for Sym Integer" $ do
      prop "divs should work on concrete" $ \(i :: Integer, j :: Integer) ->
        divs (conc i :: Sym Integer) (conc j)
          `shouldBe` if j == 0
            then merge $ throwError () :: ExceptT () UnionM SymInteger
            else mrgSingle $ conc $ i `div` j
      it "divs should work when divided by zero" $ do
        divs (ssymb "a" :: Sym Integer) (conc 0)
          `shouldBe` (merge $ throwError () :: ExceptT () UnionM SymInteger)
      it "divs should work on symbolic" $ do
        divs (ssymb "a" :: Sym Integer) (ssymb "b")
          `shouldBe` ( mrgIf
                         ((ssymb "b" :: Sym Integer) ==~ conc (0 :: Integer) :: SymBool)
                         (throwError ())
                         (mrgSingle $ Sym $ divi (ssymbTerm "a") (ssymbTerm "b")) ::
                         ExceptT () UnionM SymInteger
                     )
      prop "mods should work on concrete" $ \(i :: Integer, j :: Integer) ->
        mods (conc i :: Sym Integer) (conc j)
          `shouldBe` if j == 0
            then merge $ throwError () :: ExceptT () UnionM SymInteger
            else mrgSingle $ conc $ i `mod` j
      it "mods should work when divided by zero" $ do
        mods (ssymb "a" :: Sym Integer) (conc 0)
          `shouldBe` (merge $ throwError () :: ExceptT () UnionM SymInteger)
      it "mods should work on symbolic" $ do
        mods (ssymb "a" :: Sym Integer) (ssymb "b")
          `shouldBe` ( mrgIf
                         ((ssymb "b" :: Sym Integer) ==~ conc (0 :: Integer) :: SymBool)
                         (throwError ())
                         (mrgSingle $ Sym $ modi (ssymbTerm "a") (ssymbTerm "b")) ::
                         ExceptT () UnionM SymInteger
                     )
    describe "SOrd for Sym Integer" $ do
      prop "SOrd should work on concrete" $ \(i :: Integer, j :: Integer) -> do
        (conc i :: Sym Integer) <=~ conc j `shouldBe` (conc (i <= j) :: SymBool)
        (conc i :: Sym Integer) <~ conc j `shouldBe` (conc (i < j) :: SymBool)
        (conc i :: Sym Integer) >=~ conc j `shouldBe` (conc (i >= j) :: SymBool)
        (conc i :: Sym Integer) >~ conc j `shouldBe` (conc (i > j) :: SymBool)
        (conc i :: Sym Integer) `symCompare` conc j
          `shouldBe` (i `symCompare` j :: UnionM Ordering)
      it "SOrd should work on symbolic" $ do
        let a :: Sym Integer = ssymb "a"
        let b :: Sym Integer = ssymb "b"
        let at :: Term Integer = ssymbTerm "a"
        let bt :: Term Integer = ssymbTerm "b"
        a <=~ b `shouldBe` Sym (leNum at bt)
        a <~ b `shouldBe` Sym (ltNum at bt)
        a >=~ b `shouldBe` Sym (geNum at bt)
        a >~ b `shouldBe` Sym (gtNum at bt)
        (a `symCompare` ssymb "b" :: UnionM Ordering)
          `shouldBe` mrgIf (a <~ b) (mrgSingle LT) (mrgIf (a ==~ b) (mrgSingle EQ) (mrgSingle (GT)))
  describe "Sym BV" $ do
    let au :: Sym (BVU.UnsignedBV 4) = ssymb "a"
    let bu :: Sym (BVU.UnsignedBV 4) = ssymb "b"
    let as :: Sym (BVS.SignedBV 4) = ssymb "a"
    let bs :: Sym (BVS.SignedBV 4) = ssymb "b"
    let aut :: Term (BVU.UnsignedBV 4) = ssymbTerm "a"
    let but :: Term (BVU.UnsignedBV 4) = ssymbTerm "b"
    let ast :: Term (BVS.SignedBV 4) = ssymbTerm "a"
    let bst :: Term (BVS.SignedBV 4) = ssymbTerm "b"
    describe "Num for Sym BV" $ do
      it "fromInteger should work" $ do
        (1 :: Sym (BVU.UnsignedBV 4)) `shouldBe` Sym (concTerm 1)
        (1 :: Sym (BVS.SignedBV 4)) `shouldBe` Sym (concTerm 1)
      it "(+) for SymPrim should work" $ do
        au + bu `shouldBe` Sym (addNum aut but)
        as + bs `shouldBe` Sym (addNum ast bst)
      it "(-) for SymPrim should work" $ do
        au - bu `shouldBe` Sym (minusNum aut but)
        as - bs `shouldBe` Sym (minusNum ast bst)
      it "(*) for SymPrim should work" $ do
        au * bu `shouldBe` Sym (timesNum aut but)
        as * bs `shouldBe` Sym (timesNum ast bst)
      it "negate for SymPrim should work" $ do
        negate au `shouldBe` Sym (uminusNum aut)
        negate as `shouldBe` Sym (uminusNum ast)
      it "abs for SymPrim should work" $ do
        abs au `shouldBe` Sym (absNum aut)
        abs as `shouldBe` Sym (absNum ast)
      it "signum for SymPrim should work" $ do
        signum au `shouldBe` Sym (signumNum aut)
        signum as `shouldBe` Sym (signumNum ast)
    describe "SOrd for Sym BV" $ do
      prop "SOrd should work on concrete" $ \(i :: Integer, j :: Integer) -> do
        let iu :: BVU.UnsignedBV 4 = fromInteger i
        let ju :: BVU.UnsignedBV 4 = fromInteger j
        let is :: BVS.SignedBV 4 = fromInteger i
        let js :: BVS.SignedBV 4 = fromInteger j
        let normalizeu k = k - k `div` 16 * 16
        let normalizes k = if normalizeu k >= 8 then normalizeu k - 16 else normalizeu k
        (conc iu :: Sym (BVU.UnsignedBV 4)) <=~ conc ju `shouldBe` (conc (normalizeu i <= normalizeu j) :: SymBool)
        (conc iu :: Sym (BVU.UnsignedBV 4)) <~ conc ju `shouldBe` (conc (normalizeu i < normalizeu j) :: SymBool)
        (conc iu :: Sym (BVU.UnsignedBV 4)) >=~ conc ju `shouldBe` (conc (normalizeu i >= normalizeu j) :: SymBool)
        (conc iu :: Sym (BVU.UnsignedBV 4)) >~ conc ju `shouldBe` (conc (normalizeu i > normalizeu j) :: SymBool)
        (conc iu :: Sym (BVU.UnsignedBV 4)) `symCompare` conc ju
          `shouldBe` (normalizeu i `symCompare` normalizeu j :: UnionM Ordering)
        (conc is :: Sym (BVS.SignedBV 4)) <=~ conc js `shouldBe` (conc (normalizes i <= normalizes j) :: SymBool)
        (conc is :: Sym (BVS.SignedBV 4)) <~ conc js `shouldBe` (conc (normalizes i < normalizes j) :: SymBool)
        (conc is :: Sym (BVS.SignedBV 4)) >=~ conc js `shouldBe` (conc (normalizes i >= normalizes j) :: SymBool)
        (conc is :: Sym (BVS.SignedBV 4)) >~ conc js `shouldBe` (conc (normalizes i > normalizes j) :: SymBool)
        (conc is :: Sym (BVS.SignedBV 4)) `symCompare` conc js
          `shouldBe` (normalizes i `symCompare` normalizes j :: UnionM Ordering)
      it "SOrd should work on symbolic" $ do
        au <=~ bu `shouldBe` Sym (leNum aut but)
        au <~ bu `shouldBe` Sym (ltNum aut but)
        au >=~ bu `shouldBe` Sym (geNum aut but)
        au >~ bu `shouldBe` Sym (gtNum aut but)
        (au `symCompare` bu :: UnionM Ordering)
          `shouldBe` mrgIf (au <~ bu) (mrgSingle LT) (mrgIf (au ==~ bu) (mrgSingle EQ) (mrgSingle GT))

        as <=~ bs `shouldBe` Sym (leNum ast bst)
        as <~ bs `shouldBe` Sym (ltNum ast bst)
        as >=~ bs `shouldBe` Sym (geNum ast bst)
        as >~ bs `shouldBe` Sym (gtNum ast bst)
        (as `symCompare` bs :: UnionM Ordering)
          `shouldBe` mrgIf (as <~ bs) (mrgSingle LT) (mrgIf (as ==~ bs) (mrgSingle EQ) (mrgSingle GT))
    describe "Bits for Sym BV" $ do
      it ".&. for SymPrim should work" $ do
        au .&. bu `shouldBe` Sym (bitand aut but)
        as .&. bs `shouldBe` Sym (bitand ast bst)
      it ".|. for SymPrim should work" $ do
        au .|. bu `shouldBe` Sym (bitor aut but)
        as .|. bs `shouldBe` Sym (bitor ast bst)
      it "xor for SymPrim should work" $ do
        au `xor` bu `shouldBe` Sym (bitxor aut but)
        as `xor` bs `shouldBe` Sym (bitxor ast bst)
      it "complement for SymPrim should work" $ do
        complement au `shouldBe` Sym (bitneg aut)
        complement as `shouldBe` Sym (bitneg ast)
      it "shift for SymPrim should work" $ do
        shift au 1 `shouldBe` Sym (bitshift aut 1)
        shift as 1 `shouldBe` Sym (bitshift ast 1)
      it "rotate for SymPrim should work" $ do
        rotate au 1 `shouldBe` Sym (bitrotate aut 1)
        rotate as 1 `shouldBe` Sym (bitrotate ast 1)
      it "bitSize for SymPrim should work" $ do
        bitSizeMaybe au `shouldBe` Just 4
        bitSizeMaybe as `shouldBe` Just 4
      it "isSigned for SymPrim should work" $ do
        isSigned au `shouldBe` False
        isSigned as `shouldBe` True
      it "testBit for SymPrim would only work on concrete ones" $ do
        testBit (Conc 3 :: Sym (BVU.UnsignedBV 4)) 1 `shouldBe` True
        testBit (Conc 3 :: Sym (BVU.UnsignedBV 4)) 2 `shouldBe` False
        testBit (Conc 3 :: Sym (BVS.SignedBV 4)) 1 `shouldBe` True
        testBit (Conc 3 :: Sym (BVS.SignedBV 4)) 2 `shouldBe` False
      it "bit for SymPrim would work" $ do
        bit 1 `shouldBe` (Conc 2 :: Sym (BVU.UnsignedBV 4))
        bit 1 `shouldBe` (Conc 2 :: Sym (BVS.SignedBV 4))
      it "popCount for SymPrim would only work on concrete ones" $ do
        popCount (Conc 3 :: Sym (BVU.UnsignedBV 4)) `shouldBe` 2
        popCount (Conc 3 :: Sym (BVU.UnsignedBV 4)) `shouldBe` 2
        popCount (Conc 3 :: Sym (BVS.SignedBV 4)) `shouldBe` 2
        popCount (Conc 3 :: Sym (BVS.SignedBV 4)) `shouldBe` 2
    describe "BVConcat for Sym BV" $ do
      it "bvconcat for SymPrim" $ do
        bvconcat
          (ssymb "a" :: Sym (BVU.UnsignedBV 4))
          (ssymb "b" :: Sym (BVU.UnsignedBV 3))
          `shouldBe` Sym
            ( bvtconcat
                (ssymbTerm "a" :: Term (BVU.UnsignedBV 4))
                (ssymbTerm "b" :: Term (BVU.UnsignedBV 3))
            )
    describe "bvextend for Sym BV" $ do
      it "bvzeroExtend for SymPrim" $ do
        bvzeroExtend (Proxy @6) au `shouldBe` Sym (bvtext (Proxy @2) False aut)
        bvzeroExtend (Proxy @6) as `shouldBe` Sym (bvtext (Proxy @2) False ast)
      it "bvsignExtend for SymPrim" $ do
        bvsignExtend (Proxy @6) au `shouldBe` Sym (bvtext (Proxy @2) True aut)
        bvsignExtend (Proxy @6) as `shouldBe` Sym (bvtext (Proxy @2) True ast)
      it "bvextend for SymPrim" $ do
        bvextend (Proxy @6) au `shouldBe` Sym (bvtext (Proxy @2) False aut)
        bvextend (Proxy @6) as `shouldBe` Sym (bvtext (Proxy @2) True ast)
    describe "bvselect for Sym BV" $ do
      it "bvselect for SymPrim" $ do
        bvselect (Proxy @2) (Proxy @1) au
          `shouldBe` Sym (bvtselect (Proxy @2) (Proxy @1) aut)
        bvselect (Proxy @2) (Proxy @1) as
          `shouldBe` Sym (bvtselect (Proxy @2) (Proxy @1) ast)
    describe "conversion between Int8 and Sym BV" $ do
      it "toSym" $ do
        toSym (0 :: Int8) `shouldBe` (conc 0 :: SymSignedBV 8)
        toSym (-127 :: Int8) `shouldBe` (conc $ -127 :: SymSignedBV 8)
        toSym (-128 :: Int8) `shouldBe` (conc $ -128 :: SymSignedBV 8)
        toSym (127 :: Int8) `shouldBe` (conc 127 :: SymSignedBV 8)
      it "toCon" $ do
        toCon (conc 0 :: SymSignedBV 8) `shouldBe` Just (0 :: Int8)
        toCon (conc $ -127 :: SymSignedBV 8) `shouldBe` Just (-127 :: Int8)
        toCon (conc $ -128 :: SymSignedBV 8) `shouldBe` Just (-128 :: Int8)
        toCon (conc 127 :: SymSignedBV 8) `shouldBe` Just (127 :: Int8)
    describe "conversion between Word8 and Sym BV" $ do
      it "toSym" $ do
        toSym (0 :: Word8) `shouldBe` (conc 0 :: SymUnsignedBV 8)
        toSym (1 :: Word8) `shouldBe` (conc 1 :: SymUnsignedBV 8)
        toSym (255 :: Word8) `shouldBe` (conc 255 :: SymUnsignedBV 8)
      it "toCon" $ do
        toCon (conc 0 :: SymUnsignedBV 8) `shouldBe` Just (0 :: Word8)
        toCon (conc 1 :: SymUnsignedBV 8) `shouldBe` Just (1 :: Word8)
        toCon (conc 255 :: SymUnsignedBV 8) `shouldBe` Just (255 :: Word8)
  describe "TabularFunc" $ do
    it "apply" $ do
      (ssymb "a" :: Integer =~> Integer) # ssymb "b" `shouldBe`
        Sym (applyf (ssymbTerm "a" :: Term (Integer =-> Integer)) (ssymbTerm "b"))
