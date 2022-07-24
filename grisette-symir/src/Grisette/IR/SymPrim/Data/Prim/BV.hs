{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.IR.SymPrim.Data.Prim.BV
  ( BVTSelect (..),
    bvtselect,
    BVTConcat (..),
    bvtconcat,
    concatView,
    ConcatMatchResult (..),
    BVTExt (..),
    bvtext,
    extensionView,
    ExtensionMatchResult (..),
    selectView,
    SelectMatchResult (..),
  )
where

import Control.DeepSeq
import Data.Hashable
import Data.Proxy
import Data.Kind
import Data.Typeable (cast)
import GHC.TypeNats
import Grisette.Core.Data.Class.BitVector
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.Helpers
import Grisette.IR.SymPrim.Data.Prim.InternedTerm
import Language.Haskell.TH.Syntax hiding (Type)
import Language.Haskell.TH.Syntax.Compat
import Type.Reflection

{-
signedBVConcTermView :: forall w a. (KnownNat w) => Term a -> Maybe (SignedBV w)
signedBVConcTermView (ConcTerm _ b) = cast b
signedBVConcTermView _ = Nothing

pattern SignedBVConcTerm :: forall w a. (KnownNat w) => SignedBV w -> Term a
pattern SignedBVConcTerm b <- (signedBVConcTermView -> Just b)

signedBVTermView :: forall w a. (KnownNat w) => Term a -> Maybe (Term (SignedBV w))
signedBVTermView = castTerm

pattern SignedBVTerm :: (KnownNat w) => Term (SignedBV w) -> Term a
pattern SignedBVTerm b <- (signedBVTermView -> Just b)

unsignedBVConcTermView :: forall w a. (KnownNat w) => Term a -> Maybe (UnsignedBV w)
unsignedBVConcTermView (ConcTerm _ b) = cast b
unsignedBVConcTermView _ = Nothing

pattern UnsignedBVConcTerm :: forall w a. (KnownNat w) => UnsignedBV w -> Term a
pattern UnsignedBVConcTerm b <- (unsignedBVConcTermView -> Just b)

unsignedBVTermView :: forall w a. (KnownNat w) => Term a -> Maybe (Term (UnsignedBV w))
unsignedBVTermView = castTerm

pattern UnsignedBVTerm :: (KnownNat w) => Term (UnsignedBV w) -> Term a
pattern UnsignedBVTerm b <- (unsignedBVTermView -> Just b)

class UnderlyingBV b where
  unwrap :: b n -> BV n
  wrap :: BV n -> b n

instance UnderlyingBV BVU.UnsignedBV where
  unwrap = BVU.asBV
  wrap = BVU.UnsignedBV

instance UnderlyingBV BVS.SignedBV where
  unwrap = BVS.asBV
  wrap = BVS.SignedBV
  -}

-- select
data BVTSelect (s :: Nat -> Type) (w :: Nat) (ow :: Nat) where
  BVTSelect ::
    forall s ix w ow.
    (KnownNat ix, KnownNat w, KnownNat ow, 1 <= ow, 1 <= w, ix + w <= ow, BVSelect (s ow) ix w (s w)) =>
    Proxy ix ->
    BVTSelect s w ow

instance Eq (BVTSelect s w ow) where
  BVTSelect p1 == BVTSelect p2 = natVal p1 == natVal p2

instance Hashable (BVTSelect s w ow) where
  s `hashWithSalt` (BVTSelect p) = s `hashWithSalt` natVal p

instance Show (BVTSelect s w ow) where
  show (BVTSelect p :: BVTSelect s o ow) =
    "BVTSelect" ++ show (natVal p) ++ ":"
      ++ show (natVal p + natVal (Proxy @w))

instance Lift (BVTSelect s w ow) where
  lift = unTypeSplice . liftTyped
  liftTyped (BVTSelect (_ :: Proxy ix)) = [||(BVTSelect (Proxy @ix) :: BVTSelect s w ow)||]

instance NFData (BVTSelect s n m) where
  rnf (BVTSelect Proxy) = ()

bvtselect ::
  forall ix w ow s proxy1 proxy2.
  ( KnownNat ix,
    KnownNat w,
    KnownNat ow,
    ix + w <= ow,
    1 <= ow,
    1 <= w,
    SupportedPrim (s w),
    SupportedPrim (s ow),
    BVSelect (s ow) ix w (s w),
    Typeable s
  ) =>
  proxy1 ix ->
  proxy2 w ->
  Term (s ow) ->
  Term (s w)
bvtselect _ _ = partialEvalUnary (BVTSelect (Proxy @ix) :: BVTSelect s w ow)

instance
  (KnownNat w, KnownNat ow, 1 <= ow, 1 <= w, SupportedPrim (s w)) =>
  UnaryPartialStrategy (BVTSelect s w ow) (s ow) (s w)
  where
  extractor _ (ConcTerm _ v) = Just v
  extractor _ _ = Nothing
  constantHandler (BVTSelect p) v = Just $ concTerm $ bvselect p (Proxy @w) v
  nonConstantHandler _ _ = Nothing

instance
  ( KnownNat w,
    KnownNat ow,
    1 <= ow,
    1 <= w,
    SupportedPrim (s w),
    SupportedPrim (s ow),
    Typeable s
  ) =>
  UnaryOp (BVTSelect s w ow) (s ow) (s w)
  where
  partialEvalUnary tag@(BVTSelect _) v =
    unaryUnfoldOnce (unaryPartial @(BVTSelect s w ow) tag) (constructUnary tag) v
  pformatUnary (BVTSelect p) v =
    "(bvselect " ++ show (natVal p) ++ " " ++ show (natVal (Proxy @w)) ++ " " ++ pformat v ++ ")"

data SelectMatchResult s w ow where
  SelectMatchResult ::
    ( KnownNat ix,
      KnownNat w,
      KnownNat ow,
      ix + w <= ow,
      1 <= ow,
      1 <= w
    ) =>
    proxy ix ->
    Term (s ow) ->
    SelectMatchResult s w ow

selectView ::
  forall s w ow.
  (KnownNat w, KnownNat ow, SupportedPrim (s w), SupportedPrim (s ow), Typeable s) =>
  Term (s w) ->
  Maybe (SelectMatchResult s w ow)
selectView (UnaryTerm _ (tag :: tag) t1) =
  case ( cast tag :: Maybe (BVTSelect s w ow),
         castTerm t1 :: Maybe (Term (s ow))
       ) of
    (Just (BVTSelect (p :: Proxy ix)), Just v) ->
      Just (SelectMatchResult p v)
    _ -> Nothing
selectView _ = Nothing

-- ext
data BVTExt (s :: Nat -> Type) (w :: Nat) (w' :: Nat) where
  Zext ::
    forall s w w'.
    ( KnownNat w',
      BVExtend (s w) w' (s w'),
      KnownNat (w' - w),
      w + 1 <= w',
      1 <= w' - w
    ) =>
    BVTExt s w w'
  Sext ::
    forall s w w'.
    ( KnownNat w',
      BVExtend (s w) w' (s w'),
      KnownNat (w' - w),
      w + 1 <= w',
      1 <= w' - w
    ) =>
    BVTExt s w w'

instance Eq (BVTExt s w w') where
  Zext == Zext = True
  Sext == Sext = True
  _ == _ = False

instance Hashable (BVTExt s w w') where
  s `hashWithSalt` Zext =
    s `hashWithSalt` (0 :: Int) `hashWithSalt` typeRep @BVTExt
  s `hashWithSalt` Sext =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` typeRep @BVTExt

instance Show (BVTExt s w w') where
  show Zext = "Zext" ++ show (natVal (Proxy @w'))
  show Sext = "Sext" ++ show (natVal (Proxy @w'))

instance Lift (BVTExt s w w') where
  lift = unTypeSplice . liftTyped
  liftTyped Zext = [||Zext||]
  liftTyped Sext = [||Sext||]

instance NFData (BVTExt s w w') where
  rnf Zext = ()
  rnf Sext = ()

bvtext ::
  forall proxy w w' s.
  ( KnownNat w,
    KnownNat w',
    KnownNat (w' - w),
    1 <= w,
    1 <= w',
    w + 1 <= w',
    1 <= w' - w,
    BVExtend (s w) w' (s w'),
    SupportedPrim (s w),
    SupportedPrim (s w'),
    Typeable s
  ) =>
  proxy w' ->
  Bool ->
  Term (s w) ->
  Term (s w')
bvtext _ signed = partialEvalUnary (if signed then Sext @s @w @w' else Zext @s @w @w')

instance
  ( KnownNat w,
    KnownNat w',
    1 <= w,
    1 <= w',
    SupportedPrim (s w),
    SupportedPrim (s w')
  ) =>
  UnaryPartialStrategy (BVTExt s w w') (s w) (s w')
  where
  extractor _ (ConcTerm _ v) = Just v
  extractor _ _ = Nothing
  constantHandler tag v =
    case tag of
      Zext -> Just $ concTerm $ bvzeroExtend (Proxy @w') v
      Sext -> Just $ concTerm $ bvsignExtend (Proxy @w') v
  nonConstantHandler _ _ = Nothing

instance
  ( KnownNat w,
    KnownNat w',
    1 <= w,
    1 <= w',
    SupportedPrim (s w),
    SupportedPrim (s w'),
    Typeable s
  ) =>
  UnaryOp (BVTExt s w w') (s w) (s w')
  where
  partialEvalUnary tag v = unaryUnfoldOnce (unaryPartial @(BVTExt s w w') tag) (constructUnary tag) v
  pformatUnary Zext v = "(zext " ++ show (natVal (Proxy @w')) ++ " " ++ pformat v ++ ")"
  pformatUnary Sext v = "(sext " ++ show (natVal (Proxy @w')) ++ " " ++ pformat v ++ ")"

data ExtensionMatchResult s w w' where
  ExtensionMatchResult ::
    ( KnownNat w',
      KnownNat (w' - w),
      w + 1 <= w',
      1 <= w' - w
    ) =>
    Bool ->
    Term (s w) ->
    ExtensionMatchResult s w w'

extensionView ::
  forall s w w'.
  (KnownNat w, KnownNat w', SupportedPrim (s w), SupportedPrim (s w'), Typeable s) =>
  Term (s w') ->
  Maybe (ExtensionMatchResult s w w')
extensionView (UnaryTerm _ (tag :: tag) t1) =
  case ( cast tag :: Maybe (BVTExt s w w'),
         castTerm t1 :: Maybe (Term (s w))
       ) of
    (Just Zext, Just v) -> Just (ExtensionMatchResult False v)
    (Just Sext, Just v) -> Just (ExtensionMatchResult True v)
    _ -> Nothing
extensionView _ = Nothing

-- concat
data BVTConcat (s :: Nat -> Type) w w' w'' where
  BVTConcat :: forall s w w' w''. (KnownNat w, KnownNat w', KnownNat w'', w'' ~ (w + w'), BVConcat (s w) (s w') (s w''), Typeable s) => BVTConcat s w w' w''

instance Eq (BVTConcat s w w' w'') where
  _ == _ = True

instance Hashable (BVTConcat s w w' w'') where
  s `hashWithSalt` BVTConcat = s `hashWithSalt` typeRep @(BVTConcat s w w' w'')

instance Show (BVTConcat s w w' w'') where
  show BVTConcat = "BVTConcat"

instance Lift (BVTConcat s w w' w'') where
  lift = unTypeSplice . liftTyped
  liftTyped BVTConcat = [||(BVTConcat :: BVTConcat s w w' w'')||]

instance NFData (BVTConcat s w w' w'') where
  rnf BVTConcat = ()

--deriving (Show, Lift, Generic, NFData)

bvtconcat ::
  forall s w w' w''.
  ( KnownNat w,
    KnownNat w',
    KnownNat w'',
    w'' ~ (w + w'),
    SupportedPrim (s w),
    SupportedPrim (s w'),
    SupportedPrim (s w''),
    BVConcat (s w) (s w') (s w''),
    Typeable s
  ) =>
  Term (s w) ->
  Term (s w') ->
  Term (s w'')
bvtconcat = partialEvalBinary (BVTConcat @s @w @w' @w'')

instance
  ( KnownNat w,
    KnownNat w',
    KnownNat w'',
    w'' ~ (w + w'),
    BVConcat (s w) (s w') (s w''),
    SupportedPrim (s w),
    SupportedPrim (s w'),
    SupportedPrim (s w'')
  ) =>
  BinaryPartialStrategy (BVTConcat s w w' w'') (s w) (s w') (s w'')
  where
  extractora _ (ConcTerm _ v) = Just v
  extractora _ _ = Nothing
  extractorb _ (ConcTerm _ v) = Just v
  extractorb _ _ = Nothing
  allConstantHandler _ v1 v2 = Just $ concTerm $ bvconcat v1 v2
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ _ _ = Nothing
  nonBinaryConstantHandler _ _ _ = Nothing

instance
  ( KnownNat w,
    KnownNat w',
    KnownNat w'',
    w'' ~ (w + w'),
    BVConcat (s w) (s w') (s w''),
    SupportedPrim (s w),
    SupportedPrim (s w'),
    SupportedPrim (s w''),
    Typeable s
  ) =>
  BinaryOp (BVTConcat s w w' w'') (s w) (s w') (s w'')
  where
  partialEvalBinary tag = binaryUnfoldOnce (binaryPartial @(BVTConcat s w w' w'') tag) (constructBinary tag)
  pformatBinary _ l r = "(concat " ++ pformat l ++ " " ++ pformat r ++ ")"

{-
unsafeEqualityProof :: forall k (a :: k) (b :: k). a :~~: b
unsafeEqualityProof = unsafeCoerce (HRefl :: a :~~: a)
-}

data ConcatMatchResult s w w' w'' where
  ConcatMatchResult ::
    ( KnownNat w,
      KnownNat w',
      KnownNat w'',
      w'' ~ (w + w')
    ) =>
    Term (s w) ->
    Term (s w') ->
    ConcatMatchResult s w w' w''

concatView ::
  forall s w w' w''.
  (KnownNat w, KnownNat w', KnownNat w'', SupportedPrim (s w), SupportedPrim (s w'), Typeable s) =>
  Term (s w'') ->
  Maybe (ConcatMatchResult s w w' w'')
concatView (BinaryTerm _ (tag :: tag) t1 t2) =
  case ( cast tag :: Maybe (BVTConcat s w w' w''),
         castTerm t1 :: Maybe (Term (s w)),
         castTerm t2 :: Maybe (Term (s w'))
       ) of
    (Just BVTConcat, Just l, Just r) -> Just (ConcatMatchResult l r)
    _ -> Nothing
concatView _ = Nothing
