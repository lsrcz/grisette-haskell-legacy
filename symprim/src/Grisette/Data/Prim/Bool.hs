{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.Data.Prim.Bool
  ( trueTerm,
    falseTerm,
    pattern BoolConcTerm,
    pattern TrueTerm,
    pattern FalseTerm,
    pattern BoolTerm,
    Not (..),
    notb,
    pattern NotTerm,
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

import Control.Monad.Except
import Data.Maybe
import Data.Typeable
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm

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
data Not = Not deriving (Show)

notb :: Term Bool -> Term Bool
notb = partialEvalUnary Not

instance UnaryOp Not Bool Bool where
  partialEvalUnary _ (NotTerm tm) = tm
  partialEvalUnary _ (BoolConcTerm a) = if a then falseTerm else trueTerm
  {-
  partialEvalUnary _ (OrTerm (NotTerm n1) n2) = andb n1 (notb n2)
  partialEvalUnary _ (OrTerm n1 (NotTerm n2)) = andb (notb n1) n2
  partialEvalUnary _ (AndTerm (NotTerm n1) n2) = orb n1 (notb n2)
  partialEvalUnary _ (AndTerm n1 (NotTerm n2)) = orb (notb n1) n2
  -}
  partialEvalUnary _ tm = constructUnary Not tm
  pformatUnary t = "(! " ++ pformat t ++ ")"

pattern NotTerm :: Term Bool -> Term a
pattern NotTerm t <- UnaryTermPatt Not t

-- Eqv
data Eqv = Eqv deriving (Show)

eqterm :: (SupportedPrim a) => Term a -> Term a -> Term Bool
eqterm = partialEvalBinary Eqv

neterm :: (SupportedPrim a) => Term a -> Term a -> Term Bool
neterm l r = notb $ eqterm l r

instance SupportedPrim a => BinaryOp Eqv a a Bool where
  partialEvalBinary _ l@ConcTerm {} r@ConcTerm {} = concTerm $ l == r
  partialEvalBinary _ (NotTerm lv) (BoolTerm r)
    | lv == r = falseTerm
  partialEvalBinary _ (BoolTerm l) (NotTerm rv)
    | l == rv = falseTerm
  partialEvalBinary _ (BoolConcTerm l) (BoolConcTerm r) =
    if l == r then trueTerm else falseTerm
  partialEvalBinary _ l r
    | l == r = trueTerm
    | otherwise = constructBinary Eqv l r
  pformatBinary l r = "(== " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern EqvTerm :: (Typeable a) => Term a -> Term a -> Term Bool
pattern EqvTerm l r <- BinaryTermPatt Eqv l r

-- Or
data Or = Or deriving (Show)

orb :: Term Bool -> Term Bool -> Term Bool
orb = partialEvalBinary Or

instance BinaryOp Or Bool Bool Bool where
  partialEvalBinary _ TrueTerm _ = trueTerm
  partialEvalBinary _ FalseTerm r = r
  partialEvalBinary _ _ TrueTerm = trueTerm
  partialEvalBinary _ l FalseTerm = l
  partialEvalBinary _ l r
    | l == r = l
  partialEvalBinary _ l (NotTerm nr)
    | l == nr = trueTerm
  partialEvalBinary _ (NotTerm nl) r
    | nl == r = trueTerm
  partialEvalBinary _ (NotTerm nl) (NotTerm nr) = notb $ andb nl nr
  partialEvalBinary _ l r = constructBinary Or l r
  pformatBinary l r = "(|| " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern OrTerm :: Term Bool -> Term Bool -> Term a
pattern OrTerm l r <- BinaryTermPatt Or l r

-- And
data And = And deriving (Show)

andb :: Term Bool -> Term Bool -> Term Bool
andb = partialEvalBinary And

instance BinaryOp And Bool Bool Bool where
  partialEvalBinary _ TrueTerm r = r
  partialEvalBinary _ FalseTerm _ = falseTerm
  partialEvalBinary _ l TrueTerm = l
  partialEvalBinary _ _ FalseTerm = falseTerm
  partialEvalBinary _ l r
    | l == r = l
  partialEvalBinary _ l (NotTerm nr)
    | l == nr = falseTerm
  partialEvalBinary _ (NotTerm nl) r
    | nl == r = falseTerm
  partialEvalBinary _ (NotTerm nl) (NotTerm nr) = notb $ orb nl nr
  partialEvalBinary _ l r = constructBinary And l r
  pformatBinary l r = "(&& " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern AndTerm :: Term Bool -> Term Bool -> Term a
pattern AndTerm l r <- BinaryTermPatt And l r

data ITE = ITE deriving (Show)

iteHelper :: (Typeable a) => (Term Bool -> Term Bool) -> Term a -> Term a
iteHelper f a = fromJust $ castTerm a >>= castTerm . f

instance (SupportedPrim a) => TernaryOp ITE Bool a a a where
  partialEvalTernary _ TrueTerm ifTrue _ = ifTrue
  partialEvalTernary _ FalseTerm _ ifFalse = ifFalse
  partialEvalTernary _ _ ifTrue ifFalse | ifTrue == ifFalse = ifTrue
  partialEvalTernary _ cond (NotTerm nifTrue) (NotTerm nifFalse) =
    fromJust $ castTerm $ notb $ partialEvalTernary ITE cond nifTrue nifFalse
  partialEvalTernary _ (NotTerm ncond) ifTrue ifFalse = partialEvalTernary ITE ncond ifFalse ifTrue
  partialEvalTernary _ (ITETerm cc ct cf) (ITETerm tc tt tf) (ITETerm fc ft ff)
    | cc == tc && cc == fc = iteterm cc (iteterm ct tt ft) (iteterm cf tf ff)
  partialEvalTernary _ cond (AndTerm t1 t2) (AndTerm f1 f2)
    | t1 == f1 = fromJust $ castTerm $ andb t1 $ iteterm cond t2 f2
    | t1 == f2 = fromJust $ castTerm $ andb t1 $ iteterm cond t2 f1
    | t2 == f1 = fromJust $ castTerm $ andb t2 $ iteterm cond t1 f2
    | t2 == f2 = fromJust $ castTerm $ andb t2 $ iteterm cond t1 f1
  partialEvalTernary _ cond (AndTerm t1 t2) ifFalse
    | t1 == fromJust (castTerm ifFalse) = fromJust $ castTerm $ andb t1 $ implyb cond t2
    | t2 == fromJust (castTerm ifFalse) = fromJust $ castTerm $ andb t2 $ implyb cond t1
  partialEvalTernary _ cond ifTrue (AndTerm f1 f2)
    | f1 == fromJust (castTerm ifTrue) = fromJust $ castTerm $ andb f1 $ implyb (notb cond) f2
    | f2 == fromJust (castTerm ifTrue) = fromJust $ castTerm $ andb f2 $ implyb (notb cond) f1
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
  partialEvalTernary _ cond ifTrue ifFalse = constructTernary ITE cond ifTrue ifFalse
  pformatTernary cond l r = "(ite " ++ pformat cond ++ " " ++ pformat l ++ " " ++ pformat r ++ ")"

iteterm :: (SupportedPrim a) => Term Bool -> Term a -> Term a -> Term a
iteterm = partialEvalTernary ITE

pattern ITETerm :: (Typeable a) => Term Bool -> Term a -> Term a -> Term a
pattern ITETerm cond ifTrue ifFalse <- TernaryTermPatt ITE cond ifTrue ifFalse

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
