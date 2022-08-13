{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.IR.SymPrim.Data.Prim.Bool
  ( trueTerm,
    falseTerm,
    pattern BoolConcTerm,
    pattern TrueTerm,
    pattern FalseTerm,
    pattern BoolTerm,
    -- Not (..),
    notb,
    -- pattern NotTerm,
    Eqv (..),
    eqterm,
    neterm,
    pattern EqvTerm,
    Or (..),
    orb,
    pattern OrTerm,
    And (..),
    andb,
    pattern AndTerm,
    ITE (..),
    iteterm,
    pattern ITETerm,
    implyb,
    xorb,
    unaryUnfoldOnce,
    binaryUnfoldOnce,
  )
where

import Control.DeepSeq
import Control.Monad.Except
import Data.Hashable
import Data.Maybe
import Data.Typeable
import GHC.Generics
import Grisette.IR.SymPrim.Data.Prim.Helpers
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import {-# SOURCE #-} Grisette.IR.SymPrim.Data.Prim.Num
import Grisette.IR.SymPrim.Data.Prim.Utils
import Language.Haskell.TH.Syntax
import Unsafe.Coerce
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils

trueTerm :: Term Bool
trueTerm = concTerm True

falseTerm :: Term Bool
falseTerm = concTerm False

boolConcTermView :: forall a. Term a -> Maybe Bool
boolConcTermView (ConcTerm _ b) = cast b
boolConcTermView _ = Nothing

pattern BoolConcTerm :: Bool -> Term a
pattern BoolConcTerm b <- (boolConcTermView -> Just b)

pattern TrueTerm :: Term a
pattern TrueTerm <- BoolConcTerm True

pattern FalseTerm :: Term a
pattern FalseTerm <- BoolConcTerm False

pattern BoolTerm :: Term Bool -> Term a
pattern BoolTerm b <- (castTerm -> Just b)

-- Not
-- data Not = Not deriving (Generic, Show, Lift, NFData, Eq, Hashable)

{-notb :: Term Bool -> Term Bool
notb = partialEvalUnary Not-}

notb :: Term Bool -> Term Bool
notb (NotTerm _ tm) = tm
notb (ConcTerm _ a) = if a then falseTerm else trueTerm
notb (OrTerm (NotTerm _ n1) n2) = andb n1 (notb n2)
notb (OrTerm n1 (NotTerm _ n2)) = andb (notb n1) n2
notb (AndTerm (NotTerm _ n1) n2) = orb n1 (notb n2)
notb (AndTerm n1 (NotTerm _ n2)) = orb (notb n1) n2
notb tm = notTerm tm

{-
instance UnaryOp Not Bool Bool where
  partialEvalUnary _ (NotTerm _ tm) = tm
  partialEvalUnary _ (ConcTerm _ a) = if a then falseTerm else trueTerm
  partialEvalUnary _ (OrTerm (NotTerm _ n1) n2) = andb n1 (notb n2)
  partialEvalUnary _ (OrTerm n1 (NotTerm _ n2)) = andb (notb n1) n2
  partialEvalUnary _ (AndTerm (NotTerm _ n1) n2) = orb n1 (notb n2)
  partialEvalUnary _ (AndTerm n1 (NotTerm _ n2)) = orb (notb n1) n2
  partialEvalUnary _ tm = constructUnary Not tm
  pformatUnary _ t = "(! " ++ pformat t ++ ")"

pattern NotTerm :: Term Bool -> Term a
pattern NotTerm _ t <- UnsafeUnaryTermPatt Not t
-}

-- Eqv
data Eqv = Eqv deriving (Show, Lift, Generic, NFData, Eq, Hashable)

eqterm :: (SupportedPrim a) => Term a -> Term a -> Term Bool
eqterm = partialEvalBinary Eqv

neterm :: (SupportedPrim a) => Term a -> Term a -> Term Bool
neterm l r = notb $ eqterm l r

instance SupportedPrim a => BinaryOp Eqv a a Bool where
  partialEvalBinary _ l@ConcTerm {} r@ConcTerm {} = concTerm $ l == r
  partialEvalBinary _ l@ConcTerm {} r = eqterm r l
  partialEvalBinary _ l (BoolConcTerm rv) = if rv then unsafeCoerce l else notb $ unsafeCoerce l
  partialEvalBinary _ (NotTerm _ lv) r
    | lv == unsafeCoerce r = falseTerm
  partialEvalBinary _ l (NotTerm _ rv)
    | unsafeCoerce l == rv = falseTerm
  {-
  partialEvalBinary _ (ConcTerm l) (ConcTerm r) =
    if l == r then trueTerm else falseTerm
    -}
  partialEvalBinary
    _
    ( BinaryTerm
        _
        (Dyn (AddNum :: AddNum a))
        (Dyn (ConcTerm _ c :: Term a))
        (Dyn (v :: Term a))
      )
    (Dyn (ConcTerm _ c2 :: Term a)) =
      eqterm v (concTerm $ c2 - c)
  partialEvalBinary
    _
    (Dyn (ConcTerm _ c2 :: Term a))
    ( BinaryTerm
        _
        (Dyn (AddNum :: AddNum a))
        (Dyn (ConcTerm _ c :: Term a))
        (Dyn (v :: Term a))
      ) =
      eqterm v (concTerm $ c2 - c)
  partialEvalBinary _ l (ITETerm c t f)
    | l == t = orb c (eqterm l f)
    | l == f = orb (notb c) (eqterm l t)
  partialEvalBinary _ (ITETerm c t f) r
    | t == r = orb c (eqterm f r)
    | f == r = orb (notb c) (eqterm t r)
  partialEvalBinary _ l r
    | l == r = trueTerm
    | otherwise = constructBinary Eqv l r
  pformatBinary _ l r = "(== " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern EqvTerm :: (Typeable a) => Term a -> Term a -> Term Bool
pattern EqvTerm l r <- Unsafe1t21BinaryTermPatt Eqv l r

impliesTerm :: Term Bool -> Term Bool -> Bool
impliesTerm (ConcTerm _ True) _ = True
impliesTerm _ (ConcTerm _ False) = True
impliesTerm
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (NotTerm _ (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b))))
    | e1 == e2 && ec1 /= ec2 = True
impliesTerm a b
  | a == b = True
  | otherwise = False
{-# INLINE impliesTerm #-}

orEqFirst :: Term Bool -> Term Bool -> Bool
orEqFirst _ (ConcTerm _ False) = True
orEqFirst
  (NotTerm _ (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b)))
  (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b)))
    | e1 == e2 && ec1 /= ec2 = True
orEqFirst x y
  | x == y = True
  | otherwise = False
{-# INLINE orEqFirst #-}

orEqTrue :: Term Bool -> Term Bool -> Bool
orEqTrue (ConcTerm _ True) _ = True
orEqTrue _ (ConcTerm _ True) = True
--orEqTrue (NotTerm _ e1) (NotTerm _ e2) = andEqFalse e1 e2
orEqTrue
  (NotTerm _ (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b)))
  (NotTerm _ (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b))))
    | e1 == e2 && ec1 /= ec2 = True
orEqTrue (NotTerm _ l) r | l == r = True
orEqTrue l (NotTerm _ r) | l == r = True
orEqTrue _ _ = False
{-# INLINE orEqTrue #-}

andEqFirst :: Term Bool -> Term Bool -> Bool
andEqFirst _ (ConcTerm _ True) = True
--andEqFirst x (NotTerm _ y) = andEqFalse x y
andEqFirst
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (NotTerm _ (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b))))
    | e1 == e2 && ec1 /= ec2 = True
andEqFirst x y
  | x == y = True
  | otherwise = False
{-# INLINE andEqFirst #-}

andEqFalse :: Term Bool -> Term Bool -> Bool
andEqFalse (ConcTerm _ False) _ = True
andEqFalse _ (ConcTerm _ False) = True
-- andEqFalse (NotTerm _ e1) (NotTerm _ e2) = orEqTrue e1 e2
andEqFalse
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b)))
    | e1 == e2 && ec1 /= ec2 = True
andEqFalse (NotTerm _ x) y | x == y = True
andEqFalse x (NotTerm _ y) | x == y = True
andEqFalse _ _ = False
{-# INLINE andEqFalse #-}

-- Or
data Or = Or deriving (Show, Lift, Generic, NFData, Eq, Hashable)

orb :: Term Bool -> Term Bool -> Term Bool
orb = partialEvalBinary Or

instance BinaryOp Or Bool Bool Bool where
  partialEvalBinary _ l r
    | orEqTrue l r = trueTerm
    | orEqFirst l r = l
    | orEqFirst r l = r
  partialEvalBinary _ l r@(OrTerm r1 r2)
    | orEqTrue l r1 = trueTerm
    | orEqTrue l r2 = trueTerm
    | orEqFirst r1 l = r
    | orEqFirst r2 l = r
    | orEqFirst l r1 = orb l r2
    | orEqFirst l r2 = orb l r1
  partialEvalBinary _ l@(OrTerm l1 l2) r
    | orEqTrue l1 r = trueTerm
    | orEqTrue l2 r = trueTerm
    | orEqFirst l1 r = l
    | orEqFirst l2 r = l
    | orEqFirst r l1 = orb l2 r
    | orEqFirst r l2 = orb l1 r
  partialEvalBinary _ l (AndTerm r1 r2)
    | orEqFirst l r1 = l
    | orEqFirst l r2 = l
    | orEqTrue l r1 = orb l r2
    | orEqTrue l r2 = orb l r1
  partialEvalBinary _ (AndTerm l1 l2) r
    | orEqFirst r l1 = r
    | orEqFirst r l2 = r
    | orEqTrue l1 r = orb l2 r
    | orEqTrue l2 r = orb l1 r
  partialEvalBinary _ (NotTerm _ nl) (NotTerm _ nr) = notb $ andb nl nr
  partialEvalBinary _ l r = constructBinary Or l r
  pformatBinary _ l r = "(|| " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern OrTerm :: Term Bool -> Term Bool -> Term a
pattern OrTerm l r <- UnsafeBinaryTermPatt Or l r

-- And
data And = And deriving (Show, Lift, Generic, NFData, Eq, Hashable)

andb :: Term Bool -> Term Bool -> Term Bool
andb = partialEvalBinary And

instance BinaryOp And Bool Bool Bool where
  partialEvalBinary _ l r
    | andEqFalse l r = falseTerm
    | andEqFirst l r = l
    | andEqFirst r l = r
  partialEvalBinary _ l r@(AndTerm r1 r2)
    | andEqFalse l r1 = falseTerm
    | andEqFalse l r2 = falseTerm
    | andEqFirst r1 l = r
    | andEqFirst r2 l = r
    | andEqFirst l r1 = andb l r2
    | andEqFirst l r2 = andb l r1
  partialEvalBinary _ l@(AndTerm l1 l2) r
    | andEqFalse l1 r = falseTerm
    | andEqFalse l2 r = falseTerm
    | andEqFirst l1 r = l
    | andEqFirst l2 r = l
    | andEqFirst r l1 = andb l2 r
    | andEqFirst r l2 = andb l1 r
  partialEvalBinary _ l (OrTerm r1 r2)
    | andEqFirst l r1 = l
    | andEqFirst l r2 = l
    | andEqFalse l r1 = andb l r2
    | andEqFalse l r2 = andb l r1
  partialEvalBinary _ (OrTerm l1 l2) r
    | andEqFirst r l1 = r
    | andEqFirst r l2 = r
    | andEqFalse l1 r = andb l2 r
    | andEqFalse l2 r = andb l1 r
  partialEvalBinary _ (NotTerm _ nl) (NotTerm _ nr) = notb $ orb nl nr
  partialEvalBinary _ l r = constructBinary And l r
  pformatBinary _ l r = "(&& " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern AndTerm :: Term Bool -> Term Bool -> Term a
pattern AndTerm l r <- UnsafeBinaryTermPatt And l r

data ITE = ITE deriving (Show, Lift, Generic, NFData, Eq, Hashable)

{-
iteHelper :: (Typeable a) => (Term Bool -> Term Bool) -> Term a -> Term a
iteHelper f a = fromJust $ castTerm a >>= castTerm . f

simpleImpliesTerm :: Term Bool -> Term Bool -> Bool
simpleImpliesTerm
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (NotTerm (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b))))
    | e1 == e2 && ec1 /= ec2 = True
simpleImpliesTerm a b
  | a == b = True
  | otherwise = False
{-# INLINE simpleImpliesTerm #-}

simpleImpliesNotTerm :: Term Bool -> Term Bool -> Bool
simpleImpliesNotTerm
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b)))
    | e1 == e2 && ec1 /= ec2 = True
simpleImpliesNotTerm _ a (NotTerm _ b)
  | a == b = True
simpleImpliesNotTerm _ _ = False
{-# INLINE simpleImpliesNotTerm #-}
-}

partialEvalITEBoolLeftNot :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolLeftNot cond nIfTrue ifFalse
  | cond == nIfTrue = Just $ andb (notb cond) ifFalse -- need test
  | otherwise = case nIfTrue of
    AndTerm nt1 nt2 -> ra
      where
        ra | impliesTerm cond nt1 = Just $ iteterm cond (notb nt2) ifFalse
           | impliesTerm cond nt2 = Just $ iteterm cond (notb nt1) ifFalse
           | impliesTerm cond (notb nt1) || impliesTerm cond (notb nt2) = Just $ orb cond ifFalse
           | otherwise = Nothing
    OrTerm nt1 nt2 -> ra
      where
        ra | impliesTerm cond nt1 || impliesTerm cond nt2 = Just $ andb (notb cond) ifFalse
           | impliesTerm cond (notb nt1) = Just $ iteterm cond (notb nt2) ifFalse
           | impliesTerm cond (notb nt2) = Just $ iteterm cond (notb nt1) ifFalse
           | otherwise = Nothing
    _ -> Nothing

partialEvalITEBoolBothNot :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolBothNot cond nIfTrue nIfFalse = Just $ notb $ partialEvalITE cond nIfTrue nIfFalse

partialEvalITEBoolRightNot :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolRightNot cond ifTrue nIfFalse
  | cond == nIfFalse = Just $ orb (notb cond) ifTrue -- need test
  | otherwise = Nothing -- need work

partialEvalInferImplies :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalInferImplies cond (NotTerm _ nt1) trueRes falseRes
  | cond == nt1 = Just falseRes
  | otherwise = case (cond, nt1) of
    ( BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b),
      BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b))
      )
        | e1 == e2 && ec1 /= ec2 -> Just trueRes
    _ -> Nothing
partialEvalInferImplies
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b)))
  _
  falseRes
    | e1 == e2 && ec1 /= ec2 = Just falseRes
partialEvalInferImplies _ _ _ _ = Nothing

partialEvalITEBoolLeftAnd :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolLeftAnd cond t1 t2 ifFalse
  | t1 == ifFalse = Just $ andb t1 $ implyb cond t2
  | t2 == ifFalse = Just $ andb t2 $ implyb cond t1
  | cond == t1 = Just $ iteterm cond t2 ifFalse
  | cond == t2 = Just $ iteterm cond t1 ifFalse
  | otherwise =
    msum
      [ partialEvalInferImplies cond t1 (iteterm cond t2 ifFalse) (andb (notb cond) ifFalse),
        partialEvalInferImplies cond t2 (iteterm cond t1 ifFalse) (andb (notb cond) ifFalse)
      ]

partialEvalITEBoolBothAnd :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolBothAnd cond t1 t2 f1 f2
  | t1 == f1 = Just $ andb t1 $ iteterm cond t2 f2
  | t1 == f2 = Just $ andb t1 $ iteterm cond t2 f1
  | t2 == f1 = Just $ andb t2 $ iteterm cond t1 f2
  | t2 == f2 = Just $ andb t2 $ iteterm cond t1 f1
  | otherwise = Nothing

partialEvalITEBoolRightAnd :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolRightAnd cond ifTrue f1 f2
  | f1 == ifTrue = Just $ andb f1 $ orb cond f2
  | f2 == ifTrue = Just $ andb f2 $ orb cond f1
  | otherwise = Nothing

partialEvalITEBoolLeftOr :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolLeftOr cond t1 t2 ifFalse
  | t1 == ifFalse = Just $ orb t1 $ andb cond t2
  | t2 == ifFalse = Just $ orb t2 $ andb cond t1
  | cond == t1 = Just $ orb cond ifFalse
  | cond == t2 = Just $ orb cond ifFalse
  | otherwise =
    msum
      [ partialEvalInferImplies cond t1 (orb cond ifFalse) (iteterm cond t2 ifFalse),
        partialEvalInferImplies cond t2 (orb cond ifFalse) (iteterm cond t1 ifFalse)
      ]

partialEvalITEBoolBothOr :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolBothOr cond t1 t2 f1 f2
  | t1 == f1 = Just $ orb t1 $ iteterm cond t2 f2
  | t1 == f2 = Just $ orb t1 $ iteterm cond t2 f1
  | t2 == f1 = Just $ orb t2 $ iteterm cond t1 f2
  | t2 == f2 = Just $ orb t2 $ iteterm cond t1 f1
  | otherwise = Nothing

partialEvalITEBoolRightOr :: Term Bool -> Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolRightOr cond ifTrue f1 f2
  | f1 == ifTrue = Just $ orb f1 $ andb (notb cond) f2
  | f2 == ifTrue = Just $ orb f2 $ andb (notb cond) f1
  | otherwise = Nothing

partialEvalITEBoolLeft :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolLeft cond (AndTerm t1 t2) ifFalse =
  msum
    [ partialEvalITEBoolLeftAnd cond t1 t2 ifFalse,
      case ifFalse of
        AndTerm f1 f2 -> partialEvalITEBoolBothAnd cond t1 t2 f1 f2
        _ -> Nothing
    ]
partialEvalITEBoolLeft cond (OrTerm t1 t2) ifFalse =
  msum
    [ partialEvalITEBoolLeftOr cond t1 t2 ifFalse,
      case ifFalse of
        OrTerm f1 f2 -> partialEvalITEBoolBothOr cond t1 t2 f1 f2
        _ -> Nothing
    ]
partialEvalITEBoolLeft cond (NotTerm _ nIfTrue) ifFalse =
  msum
    [ partialEvalITEBoolLeftNot cond nIfTrue ifFalse,
      case ifFalse of
        NotTerm _ nIfFalse ->
          partialEvalITEBoolBothNot cond nIfTrue nIfFalse
        _ -> Nothing
    ]
partialEvalITEBoolLeft _ _ _ = Nothing

partialEvalITEBoolNoLeft :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolNoLeft cond ifTrue (AndTerm f1 f2) = partialEvalITEBoolRightAnd cond ifTrue f1 f2
partialEvalITEBoolNoLeft cond ifTrue (OrTerm f1 f2) = partialEvalITEBoolRightOr cond ifTrue f1 f2
partialEvalITEBoolNoLeft cond ifTrue (NotTerm _ nIfFalse) = partialEvalITEBoolRightNot cond ifTrue nIfFalse
partialEvalITEBoolNoLeft _ _ _ = Nothing

partialEvalITEBasic :: (SupportedPrim a) => Term Bool -> Term a -> Term a -> Maybe (Term a)
partialEvalITEBasic (ConcTerm _ True) ifTrue _ = Just ifTrue
partialEvalITEBasic (ConcTerm _ False) _ ifFalse = Just ifFalse
partialEvalITEBasic (NotTerm _ ncond) ifTrue ifFalse = Just $ partialEvalITE ncond ifFalse ifTrue
partialEvalITEBasic _ ifTrue ifFalse | ifTrue == ifFalse = Just ifTrue
partialEvalITEBasic (ITETerm cc ct cf) (ITETerm tc tt tf) (ITETerm fc ft ff) -- later
  | cc == tc && cc == fc = Just $ iteterm cc (iteterm ct tt ft) (iteterm cf tf ff)
partialEvalITEBasic cond (ITETerm tc tt tf) ifFalse -- later
  | cond == tc = Just $ iteterm cond tt ifFalse
  | tt == ifFalse = Just $ iteterm (orb (notb cond) tc) tt tf
  | tf == ifFalse = Just $ iteterm (andb cond tc) tt tf
  | impliesTerm cond (notb tc) = Just $ iteterm cond tf ifFalse
partialEvalITEBasic cond ifTrue (ITETerm fc ft ff) -- later
  | cond == fc = Just $ iteterm cond ifTrue ff
  | ifTrue == ft = Just $ iteterm (orb cond fc) ifTrue ff
  | ifTrue == ff = Just $ iteterm (orb cond (notb fc)) ifTrue ft
partialEvalITEBasic _ _ _ = Nothing

partialEvalITE :: forall a. (SupportedPrim a) => Term Bool -> Term a -> Term a -> Term a
partialEvalITE cond ifTrue ifFalse = fromMaybe (constructTernary ITE cond ifTrue ifFalse) $
  case eqT @a @Bool of
    Nothing -> partialEvalITEBasic cond ifTrue ifFalse
    Just Refl -> partialEvalITEBool cond ifTrue ifFalse

partialEvalITEBoolBasic :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBoolBasic cond ifTrue ifFalse
  | cond == ifTrue = Just $ orb cond ifFalse
  | cond == ifFalse = Just $ andb cond ifTrue
partialEvalITEBoolBasic cond (ConcTerm _ v) ifFalse
  | v = Just $ orb cond ifFalse
  | otherwise = Just $ andb (notb cond) ifFalse
partialEvalITEBoolBasic cond ifTrue (ConcTerm _ v)
  | v = Just $ orb (notb cond) ifTrue
  | otherwise = Just $ andb cond ifTrue
partialEvalITEBoolBasic _ _ _ = Nothing

partialEvalITEBool :: Term Bool -> Term Bool -> Term Bool -> Maybe (Term Bool)
partialEvalITEBool cond ifTrue ifFalse =
  msum
    [ partialEvalITEBasic cond ifTrue ifFalse,
      partialEvalITEBoolBasic cond ifTrue ifFalse,
      partialEvalITEBoolLeft cond ifTrue ifFalse,
      partialEvalITEBoolNoLeft cond ifTrue ifFalse
    ]

{-

  partialEvalTernary _ cond TrueTerm ifFalse =
    iteHelper (orb cond) ifFalse
  partialEvalTernary _ cond FalseTerm ifFalse =
    iteHelper (andb (notb cond)) ifFalse
  partialEvalTernary _ cond ifTrue TrueTerm =
    iteHelper (implyb cond) ifTrue
  partialEvalTernary _ cond ifTrue FalseTerm =
    iteHelper (andb cond) ifTrue
  partialEvalTernary _ cond ifTrue ifFalse
    | Just cond == castTerm ifTrue = iteHelper (orb cond) ifFalse
  partialEvalTernary _ cond ifTrue ifFalse
    | Just cond == castTerm ifFalse = iteHelper (andb cond) ifTrue

-}

instance (SupportedPrim a) => TernaryOp ITE Bool a a a where
  partialEvalTernary _ cond ifTrue ifFalse = partialEvalITE cond ifTrue ifFalse

  {-
  partialEvalTernary _ TrueTerm ifTrue _ = ifTrue
  partialEvalTernary _ FalseTerm _ ifFalse = ifFalse
  partialEvalTernary _ (NotTerm _ ncond) ifTrue ifFalse = partialEvalTernary ITE ncond ifFalse ifTrue
  partialEvalTernary _ _ ifTrue ifFalse | ifTrue == ifFalse = ifTrue
  partialEvalTernary _ (ITETerm cc ct cf) (ITETerm tc tt tf) (ITETerm fc ft ff) -- later
    | cc == tc && cc == fc = iteterm cc (iteterm ct tt ft) (iteterm cf tf ff)
  partialEvalTernary _ cond (ITETerm tc tt tf) ifFalse -- later
    | cond == tc = iteterm cond tt ifFalse
    | impliesTerm cond (notb tc) = iteterm cond tf ifFalse
    | tt == ifFalse = iteterm (orb (notb cond) tc) tt tf
    | tf == ifFalse = iteterm (andb cond tc) tt tf
  partialEvalTernary _ cond ifTrue (ITETerm fc ft ff) -- later
    | cond == fc = iteterm cond ifTrue ff
    | ifTrue == ft = iteterm (orb cond fc) ifTrue ff
    | ifTrue == ff = iteterm (orb cond (notb fc)) ifTrue ft
  partialEvalTernary _ cond (NotTerm _ nifTrue) (NotTerm _ nifFalse) =
    unsafeCoerce $ notb $ partialEvalTernary ITE cond nifTrue nifFalse
  partialEvalTernary _ cond (AndTerm t1 t2) (AndTerm f1 f2)
    | t1 == f1 = unsafeCoerce $ andb t1 $ iteterm cond t2 f2
    | t1 == f2 = unsafeCoerce $ andb t1 $ iteterm cond t2 f1
    | t2 == f1 = unsafeCoerce $ andb t2 $ iteterm cond t1 f2
    | t2 == f2 = unsafeCoerce $ andb t2 $ iteterm cond t1 f1
  partialEvalTernary _ cond (AndTerm t1 t2) ifFalse
    | t1 == unsafeCoerce ifFalse = unsafeCoerce $ andb t1 $ implyb cond t2
    | t2 == unsafeCoerce ifFalse = unsafeCoerce $ andb t2 $ implyb cond t1
    | impliesTerm cond t1 = unsafeCoerce $ iteterm cond t2 $ unsafeCoerce ifFalse
    | impliesTerm cond t2 = unsafeCoerce $ iteterm cond t1 $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t1) = unsafeCoerce $ andb (notb cond) $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t2) = unsafeCoerce $ andb (notb cond) $ unsafeCoerce ifFalse
  partialEvalTernary _ cond ifTrue (AndTerm f1 f2)
    | f1 == unsafeCoerce ifTrue = unsafeCoerce $ andb f1 $ orb cond f2
    | f2 == unsafeCoerce ifTrue = unsafeCoerce $ andb f2 $ orb cond f1
  partialEvalTernary _ cond (OrTerm t1 t2) (OrTerm f1 f2)
    | t1 == f1 = unsafeCoerce $ orb t1 $ iteterm cond t2 f2
    | t1 == f2 = unsafeCoerce $ orb t1 $ iteterm cond t2 f1
    | t2 == f1 = unsafeCoerce $ orb t2 $ iteterm cond t1 f2
    | t2 == f2 = unsafeCoerce $ orb t2 $ iteterm cond t1 f1
  partialEvalTernary _ cond (OrTerm t1 t2) ifFalse
    | t1 == unsafeCoerce ifFalse = unsafeCoerce $ orb t1 $ andb cond t2
    | t2 == unsafeCoerce ifFalse = unsafeCoerce $ orb t2 $ andb cond t1
    | impliesTerm cond t1 = unsafeCoerce $ orb cond $ unsafeCoerce ifFalse
    | impliesTerm cond t2 = unsafeCoerce $ orb cond $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t1) = unsafeCoerce $ iteterm cond t2 $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t2) = unsafeCoerce $ iteterm cond t1 $ unsafeCoerce ifFalse
  partialEvalTernary _ cond ifTrue (OrTerm f1 f2)
    | f1 == unsafeCoerce ifTrue = unsafeCoerce $ orb f1 $ andb (notb cond) f2
    | f2 == unsafeCoerce ifTrue = unsafeCoerce $ orb f2 $ andb (notb cond) f1
  partialEvalTernary _ cond TrueTerm ifFalse =
    iteHelper (orb cond) ifFalse
  partialEvalTernary _ cond FalseTerm ifFalse =
    iteHelper (andb (notb cond)) ifFalse
  partialEvalTernary _ cond ifTrue TrueTerm =
    iteHelper (implyb cond) ifTrue
  partialEvalTernary _ cond ifTrue FalseTerm =
    iteHelper (andb cond) ifTrue
  partialEvalTernary _ cond ifTrue ifFalse
    | Just cond == castTerm ifTrue = iteHelper (orb cond) ifFalse
  partialEvalTernary _ cond ifTrue ifFalse
    | Just cond == castTerm ifFalse = iteHelper (andb cond) ifTrue
  partialEvalTernary _ cond (NotTerm (AndTerm t1 t2)) ifFalse
    | impliesTerm cond t1 = unsafeCoerce $ iteterm cond (notb t2) $ unsafeCoerce ifFalse
    | impliesTerm cond t2 = unsafeCoerce $ iteterm cond (notb t1) $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t1) || impliesTerm cond (notb t2) = unsafeCoerce $ orb cond $ unsafeCoerce ifFalse
  partialEvalTernary _ cond (NotTerm (OrTerm t1 t2)) ifFalse
    | impliesTerm cond t1 || impliesTerm cond t2 = unsafeCoerce $ andb (notb cond) $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t1) = unsafeCoerce $ iteterm cond (notb t2) $ unsafeCoerce ifFalse
    | impliesTerm cond (notb t2) = unsafeCoerce $ iteterm cond (notb t1) $ unsafeCoerce ifFalse
  partialEvalTernary _ cond ifTrue ifFalse = constructTernary ITE cond ifTrue ifFalse
  -}
  pformatTernary _ cond l r = "(ite " ++ pformat cond ++ " " ++ pformat l ++ " " ++ pformat r ++ ")"

iteterm :: (SupportedPrim a) => Term Bool -> Term a -> Term a -> Term a
iteterm = partialEvalTernary ITE

pattern ITETerm :: (Typeable a) => Term Bool -> Term a -> Term a -> Term a
pattern ITETerm cond ifTrue ifFalse <- Unsafe1u2t32TernaryTermPatt ITE cond ifTrue ifFalse

implyb :: Term Bool -> Term Bool -> Term Bool
implyb l = orb (notb l)

xorb :: Term Bool -> Term Bool -> Term Bool
xorb l r = orb (andb (notb l) r) (andb l (notb r))

unaryPartialUnfoldOnce ::
  forall a b.
  (Typeable a, SupportedPrim b) =>
  PartialRuleUnary a b ->
  TotalRuleUnary a b ->
  PartialRuleUnary a b
unaryPartialUnfoldOnce partial fallback = ret
  where
    oneLevel :: TotalRuleUnary a b -> PartialRuleUnary a b
    oneLevel fallback' x = case (x, partial x) of
      (ITETerm cond vt vf, pr) ->
        let pt = partial vt
            pf = partial vf
         in case (pt, pf) of
              (Nothing, Nothing) -> pr
              (mt, mf) ->
                iteterm cond
                  <$> catchError mt (\_ -> Just $ totalize (oneLevel fallback') fallback' vt)
                  <*> catchError mf (\_ -> Just $ totalize (oneLevel fallback') fallback vf)
      (_, pr) -> pr
    ret :: PartialRuleUnary a b
    ret = oneLevel (totalize @(Term a) @(Term b) partial fallback)

unaryUnfoldOnce ::
  forall a b.
  (Typeable a, SupportedPrim b) =>
  PartialRuleUnary a b ->
  TotalRuleUnary a b ->
  TotalRuleUnary a b
unaryUnfoldOnce partial fallback = totalize (unaryPartialUnfoldOnce partial fallback) fallback

binaryPartialUnfoldOnce ::
  forall a b c.
  (Typeable a, Typeable b, SupportedPrim c) =>
  PartialRuleBinary a b c ->
  TotalRuleBinary a b c ->
  PartialRuleBinary a b c
binaryPartialUnfoldOnce partial fallback = ret
  where
    oneLevel :: (Typeable x, Typeable y) => PartialRuleBinary x y c -> TotalRuleBinary x y c -> PartialRuleBinary x y c
    oneLevel partial' fallback' x y =
      catchError
        (partial' x y)
        ( \_ ->
            catchError
              ( case x of
                  ITETerm cond vt vf -> left cond vt vf y partial' fallback'
                  _ -> Nothing
              )
              ( \_ -> case y of
                  ITETerm cond vt vf -> left cond vt vf x (flip partial') (flip fallback')
                  _ -> Nothing
              )
        )
    left ::
      (Typeable x, Typeable y) =>
      Term Bool ->
      Term x ->
      Term x ->
      Term y ->
      PartialRuleBinary x y c ->
      TotalRuleBinary x y c ->
      Maybe (Term c)
    left cond vt vf y partial' fallback' =
      let pt = partial' vt y
          pf = partial' vf y
       in case (pt, pf) of
            (Nothing, Nothing) -> Nothing
            (mt, mf) ->
              iteterm cond
                <$> catchError mt (\_ -> Just $ totalize2 (oneLevel partial' fallback') fallback' vt y)
                <*> catchError mf (\_ -> Just $ totalize2 (oneLevel partial' fallback') fallback' vf y)
    ret :: PartialRuleBinary a b c
    ret = oneLevel partial (totalize2 @(Term a) @(Term b) @(Term c) partial fallback)

binaryUnfoldOnce ::
  forall a b c.
  (Typeable a, Typeable b, SupportedPrim c) =>
  PartialRuleBinary a b c ->
  TotalRuleBinary a b c ->
  TotalRuleBinary a b c
binaryUnfoldOnce partial fallback = totalize2 (binaryPartialUnfoldOnce partial fallback) fallback
