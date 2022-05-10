{-# LANGUAGE DataKinds #-}
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

module Grisette.Data.Prim.BV
  ( pattern SignedBVConcTerm,
    pattern SignedBVTerm,
    pattern UnsignedBVConcTerm,
    pattern UnsignedBVTerm,
    BVTSelect (..),
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
    UnderlyingBV(..),
  )
where

import Control.DeepSeq
import Data.BitVector.Sized as BV
import Data.BitVector.Sized.Signed as BVS
import Data.BitVector.Sized.Unsigned as BVU
import Data.Parameterized
import Data.Typeable
import GHC.TypeNats
import Grisette.Data.Prim.Bool
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Syntax.Compat

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

-- select
data BVTSelect (w :: Nat) (ow :: Nat) where
  BVTSelect :: forall ix w ow. (KnownNat ix, KnownNat w, KnownNat ow, 1 <= ow, 1 <= w, ix + w <= ow) => Proxy ix -> BVTSelect w ow

instance Eq (BVTSelect w ow) where
  BVTSelect p1 == BVTSelect p2 = natVal p1 == natVal p2

instance Hashable (BVTSelect w ow) where
  s `hashWithSalt` (BVTSelect p) = s `hashWithSalt` natVal p

instance Show (BVTSelect w ow) where
  show (BVTSelect p :: BVTSelect o ow) =
    "BVTSelect" ++ show (natVal p) ++ ":"
      ++ show (natVal p + natVal (Proxy @w))

instance Lift (BVTSelect w ow) where
  lift = unTypeSplice . liftTyped
  liftTyped (BVTSelect (_ :: Proxy ix)) = [||(BVTSelect (Proxy @ix) :: BVTSelect w ow)||]

instance NFData (BVTSelect n m) where
  rnf (BVTSelect Proxy) = ()

bvtselect ::
  forall ix w ow s proxy1 proxy2.
  ( KnownNat ix,
    KnownNat w,
    KnownNat ow,
    ix + w <= ow,
    1 <= ow,
    1 <= w,
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s ow)
  ) =>
  proxy1 ix ->
  proxy2 w ->
  Term (s ow) ->
  Term (s w)
bvtselect _ _ = partialEvalUnary (BVTSelect @ix @w @ow (Proxy @ix))

instance
  (KnownNat w, KnownNat ow, 1 <= ow, 1 <= w, UnderlyingBV s, SupportedPrim (s w)) =>
  UnaryPartialStrategy (BVTSelect w ow) (s ow) (s w)
  where
  extractor _ (ConcTerm _ v) = Just v
  extractor _ _ = Nothing
  constantHandler (BVTSelect (_ :: Proxy ix)) v = Just $ concTerm $ wrap (select (knownNat @ix) (knownNat @w) (unwrap v))
  nonConstantHandler _ _ = Nothing

instance
  ( KnownNat w,
    KnownNat ow,
    1 <= ow,
    1 <= w,
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s ow)
  ) =>
  UnaryOp (BVTSelect w ow) (s ow) (s w)
  where
  partialEvalUnary tag@(BVTSelect (_ :: Proxy ix)) v =
    unaryUnfoldOnce (unaryPartial @(BVTSelect w ow) tag) (constructUnary tag) v
  pformatUnary (BVTSelect (_ :: Proxy ix)) v =
    "(bvselect " ++ show (natVal (Proxy @ix)) ++ " " ++ show (natVal (Proxy @w)) ++ " " ++ pformat v ++ ")"

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
  (KnownNat w, KnownNat ow, SupportedPrim (s w), SupportedPrim (s ow)) =>
  Term (s w) ->
  Maybe (SelectMatchResult s w ow)
selectView (UnaryTerm _ (tag :: tag) t1) =
  case ( cast tag :: Maybe (BVTSelect w ow),
         castTerm t1 :: Maybe (Term (s ow))
       ) of
    (Just (BVTSelect (p :: Proxy ix)), Just v) ->
      Just (SelectMatchResult p v)
    _ -> Nothing
selectView _ = Nothing

-- ext
data BVTExt (w :: Nat) (w' :: Nat) where
  Zext :: forall n w w' proxy. (KnownNat n, 1 <= n, w + 1 <= w', w' ~ (w + n), (w' - w) ~ n) => proxy n -> BVTExt w w'
  Sext :: forall n w w' proxy. (KnownNat n, 1 <= n, w + 1 <= w', w' ~ (w + n), (w' - w) ~ n) => proxy n -> BVTExt w w'

instance Eq (BVTExt w w') where
  Zext (_ :: proxy n) == Zext (_ :: proxy2 n2) = knownNat @n == knownNat @n2
  Sext (_ :: proxy n) == Sext (_ :: proxy2 n2) = knownNat @n == knownNat @n2
  _ == _ = False

instance Hashable (BVTExt w w') where
  s `hashWithSalt` (Zext (_ :: proxy n)) =
    s `hashWithSalt` (0 :: Int) `hashWithSalt` typeRep (Proxy @BVTExt) `hashWithSalt` (knownNat @n)
  s `hashWithSalt` (Sext (_ :: proxy n)) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` typeRep (Proxy @BVTExt) `hashWithSalt` (knownNat @n)

instance Show (BVTExt w w') where
  show (Zext p) = "Zext" ++ show (natVal p)
  show (Sext p) = "Sext" ++ show (natVal p)

instance Lift (BVTExt w w') where
  lift = unTypeSplice . liftTyped
  liftTyped (Zext (_ :: proxy n)) = [||(Zext (Proxy @n) :: BVTExt w w')||]
  liftTyped (Sext (_ :: proxy n)) = [||(Sext (Proxy @n) :: BVTExt w w')||]

instance NFData (BVTExt w w') where
  rnf (Zext _) = ()
  rnf (Sext _) = ()

bvtext ::
  forall n w w' s proxy.
  ( KnownNat n,
    KnownNat w,
    KnownNat w',
    w' ~ (w + n),
    1 <= w,
    1 <= n,
    1 <= w',
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s w')
  ) =>
  proxy n ->
  Bool ->
  Term (s w) ->
  Term (s w')
bvtext p signed =
  let e1 = leqProof (Proxy @1) (Proxy @n)
      e2 = leqRefl (Proxy @w)
      e3 = leqAdd2 e2 e1
      e4 = plusComm (Proxy @w) (Proxy @n)
      e5 = plusMinusCancel (Proxy @n) (Proxy @w)
   in case (e3, e4, e5) of
        (LeqProof, Refl, Refl) ->
          partialEvalUnary (if signed then Sext @n @w @w' p else Zext @n @w @w' p)

instance
  ( KnownNat w,
    KnownNat w',
    1 <= w,
    1 <= w',
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s w')
  ) =>
  UnaryPartialStrategy (BVTExt w w') (s w) (s w')
  where
  extractor _ (ConcTerm _ v) = Just v
  extractor _ _ = Nothing
  constantHandler tag v =
    case tag of
      Zext p ->
        let wleqw = leqProof (Proxy @w) (Proxy @w)
            oneleqn = leqProof (Proxy @1) p
            wplus1leqw' = leqAdd2 wleqw oneleqn
         in case wplus1leqw' of
              LeqProof ->
                Just $ concTerm $ wrap $ zext (knownNat @w') (unwrap v)
      Sext p ->
        let wleqw = leqProof (Proxy @w) (Proxy @w)
            oneleqn = leqProof (Proxy @1) p
            wplus1leqw' = leqAdd2 wleqw oneleqn
         in case wplus1leqw' of
              LeqProof ->
                Just $ concTerm $ wrap $ sext (knownNat @w) (knownNat @w') (unwrap v)
  nonConstantHandler _ _ = Nothing

instance
  ( KnownNat w,
    KnownNat w',
    1 <= w,
    1 <= w',
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s w')
  ) =>
  UnaryOp (BVTExt w w') (s w) (s w')
  where
  partialEvalUnary tag v = unaryUnfoldOnce (unaryPartial @(BVTExt w w') tag) (constructUnary tag) v
  pformatUnary (Zext p) v = "(zext " ++ show (natVal p) ++ " " ++ pformat v ++ ")"
  pformatUnary (Sext p) v = "(sext " ++ show (natVal p) ++ " " ++ pformat v ++ ")"

data ExtensionMatchResult s w w' where
  ExtensionMatchResult ::
    ( KnownNat n,
      KnownNat w,
      KnownNat w',
      1 <= n,
      w + 1 <= w',
      w' ~ (w + n),
      (w' - w) ~ n
    ) =>
    proxy n ->
    Bool ->
    Term (s w) ->
    ExtensionMatchResult s w w'

extensionView ::
  forall s w w'.
  (KnownNat w, KnownNat w', SupportedPrim (s w), SupportedPrim (s w')) =>
  Term (s w') ->
  Maybe (ExtensionMatchResult s w w')
extensionView (UnaryTerm _ (tag :: tag) t1) =
  case ( cast tag :: Maybe (BVTExt w w'),
         castTerm t1 :: Maybe (Term (s w))
       ) of
    (Just (Zext p), Just v) -> Just (ExtensionMatchResult p False v)
    (Just (Sext p), Just v) -> Just (ExtensionMatchResult p True v)
    _ -> Nothing
extensionView _ = Nothing

-- concat
data BVTConcat w w' w'' where
  BVTConcat :: (KnownNat w, KnownNat w', KnownNat w'', w'' ~ (w + w')) => BVTConcat w w' w''
  deriving (Typeable)

instance Eq (BVTConcat w w' w'') where
  _ == _ = True

instance Hashable (BVTConcat w w' w'') where
  s `hashWithSalt` BVTConcat = s `hashWithSalt` typeRep (Proxy @(BVTConcat w w' w''))

instance Show (BVTConcat w w' w'') where
  show BVTConcat = "BVTConcat"

instance Lift (BVTConcat w w' w'') where
  lift = unTypeSplice . liftTyped
  liftTyped BVTConcat = [||(BVTConcat :: BVTConcat w w' w'')||]

instance NFData (BVTConcat w w' w'') where
  rnf BVTConcat = ()

--deriving (Show, Lift, Generic, NFData)

bvtconcat ::
  forall w w' w'' s.
  ( KnownNat w,
    KnownNat w',
    KnownNat w'',
    w'' ~ (w + w'),
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s w'),
    SupportedPrim (s w'')
  ) =>
  Term (s w) ->
  Term (s w') ->
  Term (s w'')
bvtconcat = partialEvalBinary (BVTConcat @w @w' @w'')

instance
  ( KnownNat w,
    KnownNat w',
    KnownNat w'',
    w'' ~ (w + w'),
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s w'),
    SupportedPrim (s w'')
  ) =>
  BinaryPartialStrategy (BVTConcat w w' w'') (s w) (s w') (s w'')
  where
  extractora _ (ConcTerm _ v) = Just v
  extractora _ _ = Nothing
  extractorb _ (ConcTerm _ v) = Just v
  extractorb _ _ = Nothing
  allConstantHandler _ v1 v2 = Just $ concTerm $ wrap $ BV.concat (knownNat @w) (knownNat @w') (unwrap v1) (unwrap v2)
  leftConstantHandler _ _ _ = Nothing
  rightConstantHandler _ _ _ = Nothing
  nonBinaryConstantHandler _ _ _ = Nothing

instance
  ( KnownNat w,
    KnownNat w',
    KnownNat w'',
    w'' ~ (w + w'),
    UnderlyingBV s,
    SupportedPrim (s w),
    SupportedPrim (s w'),
    SupportedPrim (s w'')
  ) =>
  BinaryOp (BVTConcat w w' w'') (s w) (s w') (s w'')
  where
  partialEvalBinary tag = binaryUnfoldOnce (binaryPartial @(BVTConcat w w' w'') tag) (constructBinary tag)
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
  (KnownNat w, KnownNat w', KnownNat w'', SupportedPrim (s w), SupportedPrim (s w')) =>
  Term (s w'') ->
  Maybe (ConcatMatchResult s w w' w'')
concatView (BinaryTerm _ (tag :: tag) t1 t2) =
  case ( cast tag :: Maybe (BVTConcat w w' w''),
         castTerm t1 :: Maybe (Term (s w)),
         castTerm t2 :: Maybe (Term (s w'))
       ) of
    (Just BVTConcat, Just l, Just r) -> Just (ConcatMatchResult l r)
    _ -> Nothing
concatView _ = Nothing
