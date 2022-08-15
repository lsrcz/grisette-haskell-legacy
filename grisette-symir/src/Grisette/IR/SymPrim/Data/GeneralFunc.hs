{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Grisette.IR.SymPrim.Data.GeneralFunc where

import Control.DeepSeq
import Data.Hashable
import GHC.Generics
import Grisette.Core.Data.Class.Function
import Grisette.Core.Data.MemoUtils
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Language.Haskell.TH.Syntax
import Type.Reflection
import Unsafe.Coerce
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.Num
import Grisette.IR.SymPrim.Data.Prim.Bits
import Grisette.IR.SymPrim.Data.Prim.BV

data FuncArg = FuncArg deriving (Show, Eq, Generic, Ord, Lift, Hashable, NFData)

data (-->) a b where
  GeneralFunc :: (SupportedPrim a, SupportedPrim b) => TypeRep a -> Symbol -> Term b -> (a --> b)

infixr 0 -->

instance Eq (a --> b) where
  GeneralFunc _ sym1 tm1 == GeneralFunc _ sym2 tm2 = sym1 == sym2 && tm1 == tm2

instance Show (a --> b) where
  show (GeneralFunc ta sym tm) = "\\(" ++ show (TermSymbol ta sym) ++ ") -> " ++ pformat tm

instance Lift (a --> b) where
  liftTyped (GeneralFunc _ sym tm) = [||GeneralFunc (typeRep @a) sym tm||]

instance Hashable (a --> b) where
  s `hashWithSalt` (GeneralFunc _ sym tm) = s `hashWithSalt` sym `hashWithSalt` tm

instance NFData (a --> b) where
  rnf (GeneralFunc p sym tm) = rnf (SomeTypeRep p) `seq` rnf sym `seq` rnf tm

instance (SupportedPrim a, SupportedPrim b) => SupportedPrim (a --> b) where
  type PrimConstraint (a --> b) = (SupportedPrim a, SupportedPrim b)
  defaultValue = GeneralFunc typeRep (WithInfo (SimpleSymbol "a") FuncArg) (concTerm defaultValue)

instance (SupportedPrim a, SupportedPrim b) => Function (a --> b) where
  type Arg (a --> b) = Term a
  type Ret (a --> b) = Term b
  (GeneralFunc ta arg tm) # v = subst (TermSymbol ta arg) v tm

subst :: forall a b. (SupportedPrim a, SupportedPrim b) => TermSymbol -> Term a -> Term b -> Term b
subst sym@(TermSymbol tc _) term input = case eqTypeRep tc (typeRep @a) of
  Just HRefl -> gov input
  Nothing -> error "Bad symbol type"
  where
    gov :: (SupportedPrim x) => Term x -> Term x
    gov b = case go (SomeTerm b) of
      SomeTerm v -> unsafeCoerce v
    go :: SomeTerm -> SomeTerm
    go = htmemo $ \stm@(SomeTerm (tm :: Term v)) ->
      case tm of
        ConcTerm _ cv -> case (typeRep :: TypeRep v) of
          App (App gf _) _ ->
            case eqTypeRep gf (typeRep @(-->)) of
              Just HRefl -> case cv of
                GeneralFunc p1 sym1 tm1 ->
                  if TermSymbol p1 sym1 == sym
                    then stm
                    else SomeTerm $ concTerm $ GeneralFunc p1 sym1 (gov tm1)
              Nothing -> stm
          _ -> stm
        SymbTerm _ ts -> SomeTerm $ if ts == sym then unsafeCoerce term else tm
        UnaryTerm _ tag te -> SomeTerm $ partialEvalUnary tag (gov te)
        BinaryTerm _ tag te te' -> SomeTerm $ partialEvalBinary tag (gov te) (gov te')
        TernaryTerm _ tag op1 op2 op3 -> SomeTerm $ partialEvalTernary tag (gov op1) (gov op2) (gov op3)
        NotTerm _ op -> SomeTerm $ pevalNotTerm (gov op)
        OrTerm _ op1 op2 -> SomeTerm $ pevalOrTerm (gov op1) (gov op2)
        AndTerm _ op1 op2 -> SomeTerm $ pevalAndTerm (gov op1) (gov op2)
        EqvTerm _ op1 op2 -> SomeTerm $ pevalEqvTerm (gov op1) (gov op2)
        ITETerm _ c op1 op2 -> SomeTerm $ pevalITETerm (gov c) (gov op1) (gov op2)
        AddNumTerm _ op1 op2 -> SomeTerm $ pevalAddNumTerm (gov op1) (gov op2)
        UMinusNumTerm _ op -> SomeTerm $ pevalUMinusNumTerm (gov op)
        TimesNumTerm _ op1 op2 -> SomeTerm $ pevalTimesNumTerm (gov op1) (gov op2)
        AbsNumTerm _ op -> SomeTerm $ pevalAbsNumTerm (gov op)
        SignumNumTerm _ op -> SomeTerm $ pevalSignumNumTerm (gov op)
        LTNumTerm _ op1 op2 -> SomeTerm $ pevalLtNumTerm (gov op1) (gov op2)
        LENumTerm _ op1 op2 -> SomeTerm $ pevalLeNumTerm (gov op1) (gov op2)
        AndBitsTerm _ op1 op2 -> SomeTerm $ pevalAndBitsTerm (gov op1) (gov op2)
        OrBitsTerm _ op1 op2 -> SomeTerm $ pevalOrBitsTerm (gov op1) (gov op2)
        XorBitsTerm _ op1 op2 -> SomeTerm $ pevalXorBitsTerm (gov op1) (gov op2)
        ComplementBitsTerm _ op -> SomeTerm $ pevalComplementBitsTerm (gov op)
        ShiftBitsTerm _ op n -> SomeTerm $ pevalShiftBitsTerm (gov op) n
        RotateBitsTerm _ op n -> SomeTerm $ pevalRotateBitsTerm (gov op) n
        BVConcatTerm _ op1 op2 -> SomeTerm $ pevalBVConcatTerm (gov op1) (gov op2)
