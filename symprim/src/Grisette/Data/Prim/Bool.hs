{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
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

import Control.DeepSeq
import Control.Monad.Except
import Data.Maybe
import Data.Typeable
import GHC.Generics
import Grisette.Data.Prim.Helpers
import Grisette.Data.Prim.InternedTerm
import {-# SOURCE #-} Grisette.Data.Prim.Num
import Grisette.Data.Prim.Utils
import Language.Haskell.TH.Syntax

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
data Not = Not deriving (Generic, Show, Lift, NFData)

notb :: Term Bool -> Term Bool
notb = partialEvalUnary Not

instance UnaryOp Not Bool Bool where
  partialEvalUnary _ (NotTerm tm) = tm
  partialEvalUnary _ (BoolConcTerm a) = if a then falseTerm else trueTerm
  partialEvalUnary _ (OrTerm (NotTerm n1) n2) = andb n1 (notb n2)
  partialEvalUnary _ (OrTerm n1 (NotTerm n2)) = andb (notb n1) n2
  partialEvalUnary _ (AndTerm (NotTerm n1) n2) = orb n1 (notb n2)
  partialEvalUnary _ (AndTerm n1 (NotTerm n2)) = orb (notb n1) n2
  partialEvalUnary _ tm = constructUnary Not tm
  pformatUnary _ t = "(! " ++ pformat t ++ ")"

pattern NotTerm :: Term Bool -> Term a
pattern NotTerm t <- UnsafeUnaryTermPatt Not t

-- Eqv
data Eqv = Eqv deriving (Show, Lift, Generic, NFData)

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
  partialEvalBinary _ (BinaryTerm _ (Dyn (AddNum :: AddNum a))
    (Dyn (ConcTerm _ c :: Term a)) (Dyn (v :: Term a))) (Dyn (ConcTerm _ c2 :: Term a)) =
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
impliesTerm TrueTerm _ = True
impliesTerm _ FalseTerm = True
impliesTerm
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (NotTerm (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b))))
    | e1 == e2 && ec1 /= ec2 = True
impliesTerm a b
  | a == b = True
  | otherwise = False

orEqFirst :: Term Bool -> Term Bool -> Bool
orEqFirst _ FalseTerm = True
orEqFirst
  (NotTerm (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b)))
  (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b)))
    | e1 == e2 && ec1 /= ec2 = True
orEqFirst x y
  | x == y = True
  | otherwise = False

orEqTrue :: Term Bool -> Term Bool -> Bool
orEqTrue TrueTerm _ = True
orEqTrue _ TrueTerm = True
orEqTrue (NotTerm e1) (NotTerm e2) = andEqFalse e1 e2
orEqTrue l r
  | l == notb r = True
  | otherwise = False

andEqFirst :: Term Bool -> Term Bool -> Bool
andEqFirst _ TrueTerm = True
andEqFirst x (NotTerm y) = andEqFalse x y
andEqFirst x y
  | x == y = True
  | otherwise = False

andEqFalse :: Term Bool -> Term Bool -> Bool
andEqFalse FalseTerm _ = True
andEqFalse _ FalseTerm = True
andEqFalse (NotTerm e1) (NotTerm e2) = orEqTrue e1 e2
andEqFalse
  (BinaryTerm _ (Dyn Eqv) (e1 :: Term a) (ec1@(ConcTerm _ _) :: Term b))
  (BinaryTerm _ (Dyn Eqv) (Dyn (e2 :: Term a)) (Dyn (ec2@(ConcTerm _ _) :: Term b)))
    | e1 == e2 && ec1 /= ec2 = True
andEqFalse x y
  | x == notb y = True
  | otherwise = False

-- Or
data Or = Or deriving (Show, Lift, Generic, NFData)

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
    | orEqFirst l r1 = orb l r2
    | orEqFirst l r2 = orb l r1
    | orEqFirst r1 l = r
    | orEqFirst r2 l = r
  partialEvalBinary _ l@(OrTerm l1 l2) r
    | orEqTrue l1 r = trueTerm
    | orEqTrue l2 r = trueTerm
    | orEqFirst l1 r = l
    | orEqFirst l2 r = l
    | orEqFirst r l1 = orb l2 r
    | orEqFirst r l2 = orb l1 r
  partialEvalBinary _ l (AndTerm r1 r2)
    | orEqTrue l r1 = orb l r2
    | orEqTrue l r2 = orb l r1
    | orEqFirst l r1 = l
    | orEqFirst l r2 = l
  partialEvalBinary _ (AndTerm l1 l2) r
    | orEqTrue l1 r = orb l2 r
    | orEqTrue l2 r = orb l1 r
    | orEqFirst r l1 = r
    | orEqFirst r l2 = r
  partialEvalBinary _ (NotTerm nl) (NotTerm nr) = notb $ andb nl nr
  partialEvalBinary _ l r = constructBinary Or l r
  pformatBinary _ l r = "(|| " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern OrTerm :: Term Bool -> Term Bool -> Term a
pattern OrTerm l r <- UnsafeBinaryTermPatt Or l r

-- And
data And = And deriving (Show, Lift, Generic, NFData)

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
    | andEqFirst l r1 = andb l r2
    | andEqFirst l r2 = andb l r1
    | andEqFirst r1 l = r
    | andEqFirst r2 l = r
  partialEvalBinary _ l@(AndTerm l1 l2) r
    | andEqFalse l1 r = falseTerm
    | andEqFalse l2 r = falseTerm
    | andEqFirst l1 r = l
    | andEqFirst l2 r = l
    | andEqFirst r l1 = andb l2 r
    | andEqFirst r l2 = andb l1 r
  partialEvalBinary _ l (OrTerm r1 r2)
    | andEqFalse l r1 = andb l r2
    | andEqFalse l r2 = andb l r1
    | andEqFirst l r1 = l
    | andEqFirst l r2 = l
  partialEvalBinary _ (OrTerm l1 l2) r
    | andEqFalse l1 r = andb l2 r
    | andEqFalse l2 r = andb l1 r
    | andEqFirst r l1 = r
    | andEqFirst r l2 = r
  partialEvalBinary _ (NotTerm nl) (NotTerm nr) = notb $ orb nl nr
  partialEvalBinary _ l r = constructBinary And l r
  pformatBinary _ l r = "(&& " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern AndTerm :: Term Bool -> Term Bool -> Term a
pattern AndTerm l r <- UnsafeBinaryTermPatt And l r

data ITE = ITE deriving (Show, Lift, Generic, NFData)

iteHelper :: (Typeable a) => (Term Bool -> Term Bool) -> Term a -> Term a
iteHelper f a = fromJust $ castTerm a >>= castTerm . f

instance (SupportedPrim a) => TernaryOp ITE Bool a a a where
  partialEvalTernary _ TrueTerm ifTrue _ = ifTrue
  partialEvalTernary _ FalseTerm _ ifFalse = ifFalse
  partialEvalTernary _ _ ifTrue ifFalse | ifTrue == ifFalse = ifTrue
  partialEvalTernary _ cond (NotTerm nifTrue) (NotTerm nifFalse) =
    fromJust $ castTerm $ notb $ partialEvalTernary ITE cond nifTrue nifFalse
  partialEvalTernary _ (NotTerm ncond) ifTrue ifFalse = partialEvalTernary ITE ncond ifFalse ifTrue
  partialEvalTernary _ (ITETerm cc ct cf) (ITETerm tc tt tf) (ITETerm fc ft ff) -- later
    | cc == tc && cc == fc = iteterm cc (iteterm ct tt ft) (iteterm cf tf ff)
  partialEvalTernary _ cond (ITETerm tc tt tf) ifFalse -- later
    | cond == tc = iteterm cond tt ifFalse
    | cond == notb tc = iteterm cond tf ifFalse
    | tt == ifFalse = iteterm (orb (notb cond) tc) tt tf
    | tf == ifFalse = iteterm (andb cond tc) tt tf
  partialEvalTernary _ cond ifTrue (ITETerm fc ft ff) -- later
    | cond == fc = iteterm cond ifTrue ff
    | cond == notb fc = iteterm cond ifTrue ft
    | ifTrue == ft = iteterm (orb cond fc) ifTrue ff
    | ifTrue == ff = iteterm (orb cond (notb fc)) ifTrue ft
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
  partialEvalTernary _ cond (OrTerm t1 t2) ifFalse
    | impliesTerm cond t1 = fromJust $ castTerm $ orb cond $ fromJust $ castTerm ifFalse
    | impliesTerm cond t2 = fromJust $ castTerm $ orb cond $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t1) = fromJust $ castTerm $ iteterm cond t2 $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t2) = fromJust $ castTerm $ iteterm cond t1 $ fromJust $ castTerm ifFalse
  {-partialEvalTernary _ cond (OrTerm (NotTerm t1) t2) ifFalse
    | impliesTerm cond t1 = fromJust $ castTerm $ iteterm cond t2 $ fromJust $ castTerm ifFalse
  partialEvalTernary _ cond (OrTerm t1 (NotTerm t2)) ifFalse
    | impliesTerm cond t2 = fromJust $ castTerm $ iteterm cond t1 $ fromJust $ castTerm ifFalse-}

  partialEvalTernary _ cond (AndTerm t1 t2) ifFalse
    | impliesTerm cond t1 = fromJust $ castTerm $ iteterm cond t2 $ fromJust $ castTerm ifFalse
    | impliesTerm cond t2 = fromJust $ castTerm $ iteterm cond t1 $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t1) = fromJust $ castTerm $ andb (notb cond) $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t2) = fromJust $ castTerm $ andb (notb cond) $ fromJust $ castTerm ifFalse
  {-
  partialEvalTernary _ cond (AndTerm (NotTerm t1) _) ifFalse
    | impliesTerm cond t1 = fromJust $ castTerm $ andb (notb cond) $ fromJust $ castTerm ifFalse
  partialEvalTernary _ cond (AndTerm _ (NotTerm t2)) ifFalse
    | impliesTerm cond t2 = fromJust $ castTerm $ andb (notb cond) $ fromJust $ castTerm ifFalse
    -}
  {-
  partialEvalTernary _ cond (AndTerm (ITETerm tc t1 t2) t3) ifFalse
    | impliesTerm cond tc = iteterm cond (fromJust $ castTerm $ andb t1 t3) ifFalse
  partialEvalTernary _ cond (AndTerm t1 (ITETerm tc t2 t3)) ifFalse
    | impliesTerm cond tc = iteterm cond (fromJust $ castTerm $ andb t1 t2) ifFalse
    -}

  partialEvalTernary _ cond (NotTerm (AndTerm t1 t2)) ifFalse
    | impliesTerm cond t1 = fromJust $ castTerm $ iteterm cond (notb t2) $ fromJust $ castTerm ifFalse
    | impliesTerm cond t2 = fromJust $ castTerm $ iteterm cond (notb t1) $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t1) || impliesTerm cond (notb t2) = fromJust $ castTerm $ orb cond $ fromJust $ castTerm ifFalse
  partialEvalTernary _ cond (NotTerm (OrTerm t1 t2)) ifFalse
    | impliesTerm cond t1 || impliesTerm cond t2 = fromJust $ castTerm $ andb (notb cond) $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t1) = fromJust $ castTerm $ iteterm cond (notb t2) $ fromJust $ castTerm ifFalse
    | impliesTerm cond (notb t2) = fromJust $ castTerm $ iteterm cond (notb t1) $ fromJust $ castTerm ifFalse
  {-
  partialEvalTernary _ cond (OrTerm (NotTerm t1) t2) ifFalse
    | cond == t1 = fromJust $ castTerm $ iteterm cond t2 (fromJust $ castTerm ifFalse)
  partialEvalTernary _ cond (OrTerm t1 (NotTerm t2)) ifFalse
    | cond == t2 = fromJust $ castTerm $ iteterm cond t1 (fromJust $ castTerm ifFalse)

  partialEvalTernary _ cond (OrTerm t1 t2) ifFalse
    | cond == t1 = fromJust $ castTerm $ orb cond (fromJust $ castTerm ifFalse)
    | cond == t2 = fromJust $ castTerm $ orb cond (fromJust $ castTerm ifFalse)
  partialEvalTernary _ cond (AndTerm t1 t2) ifFalse
    | cond == t1 = fromJust $ castTerm $ iteterm cond t2 (fromJust $ castTerm ifFalse)
    | cond == t2 = fromJust $ castTerm $ iteterm cond t1 (fromJust $ castTerm ifFalse)
    -}
  {-
    partialEvalTernary _ cond@(EqvTerm (ea :: Term Integer) (IntegerConcTerm c))
      (OrTerm (EqvTerm (eb :: Term Integer) (IntegerConcTerm c2)) t2) ifFalse
      | ea == eb && c /= c2 = fromJust $ castTerm $ iteterm cond t2 (fromJust $ castTerm ifFalse)
    partialEvalTernary _ cond@(EqvTerm (ea :: Term Integer) (IntegerConcTerm c))
      (OrTerm t2 (EqvTerm (eb :: Term Integer) (IntegerConcTerm c2))) ifFalse
      | ea == eb && c /= c2 = fromJust $ castTerm $ iteterm cond t2 (fromJust $ castTerm ifFalse)

    partialEvalTernary _ cond@(EqvTerm (ea :: Term Integer) (IntegerConcTerm c))
      (OrTerm (NotTerm (EqvTerm (eb :: Term Integer) (IntegerConcTerm c2))) t2) ifFalse
      | ea == eb && c /= c2 = fromJust $ castTerm $ orb cond (fromJust $ castTerm ifFalse)
    partialEvalTernary _ cond@(EqvTerm (ea :: Term Integer) (IntegerConcTerm c))
      (OrTerm t2 (NotTerm (EqvTerm (eb :: Term Integer) (IntegerConcTerm c2)))) ifFalse
      | ea == eb && c /= c2 = fromJust $ castTerm $ orb cond (fromJust $ castTerm ifFalse)
      -}

  partialEvalTernary
    _
    cond@(BinaryTerm _ (Dyn Eqv) (ea :: Term x) (Dyn (ec1@(ConcTerm _ _) :: Term x)))
    (ITETerm (EqvTerm (eb :: Term x) ec2@(ConcTerm _ _)) _ t2)
    ifFalse
      | ea == eb && ec1 /= ec2 = fromJust $ castTerm $ iteterm cond t2 (fromJust $ castTerm ifFalse)
  partialEvalTernary
    _
    cond@(BinaryTerm _ (Dyn Eqv) (ea :: Term x) (Dyn (ConcTerm _ c1 :: Term x)))
    (ITETerm (NotTerm (EqvTerm (eb :: Term x) (ConcTerm _ c2))) t1 _)
    ifFalse
      | ea == eb && c1 /= c2 = fromJust $ castTerm $ iteterm cond t1 (fromJust $ castTerm ifFalse)
  partialEvalTernary _ cond ifTrue ifFalse = constructTernary ITE cond ifTrue ifFalse
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
