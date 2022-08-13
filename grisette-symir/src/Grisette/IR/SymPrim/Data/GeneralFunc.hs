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
import Data.Proxy
import Data.Typeable
import GHC.Generics
import Grisette.Core.Data.Class.Function
import Grisette.Core.Data.MemoUtils
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Language.Haskell.TH.Syntax
import qualified Type.Reflection as R
import Unsafe.Coerce
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.Bool

data FuncArg = FuncArg deriving (Show, Eq, Generic, Ord, Lift, Hashable, NFData)

data (-->) a b where
  GeneralFunc :: (SupportedPrim a, SupportedPrim b) => Proxy a -> Symbol -> Term b -> (a --> b)

infixr 0 -->

instance Eq (a --> b) where
  GeneralFunc _ sym1 tm1 == GeneralFunc _ sym2 tm2 = sym1 == sym2 && tm1 == tm2

instance Show (a --> b) where
  show (GeneralFunc _ sym tm) = "\\(" ++ show (TermSymbol (Proxy @a) sym) ++ ") -> " ++ pformat tm

instance Lift (a --> b) where
  liftTyped (GeneralFunc _ sym tm) = [||GeneralFunc Proxy sym tm||]

instance Hashable (a --> b) where
  s `hashWithSalt` (GeneralFunc _ sym tm) = s `hashWithSalt` sym `hashWithSalt` tm

instance NFData (a --> b) where
  rnf (GeneralFunc p sym tm) = rnf p `seq` rnf sym `seq` rnf tm

instance (SupportedPrim a, SupportedPrim b) => SupportedPrim (a --> b) where
  type PrimConstraint (a --> b) = (SupportedPrim a, SupportedPrim b)
  defaultValue = GeneralFunc Proxy (WithInfo (SimpleSymbol "a") FuncArg) (concTerm defaultValue)

instance (SupportedPrim a, SupportedPrim b) => Function (a --> b) where
  type Arg (a --> b) = Term a
  type Ret (a --> b) = Term b
  (GeneralFunc _ arg tm) # v = subst (TermSymbol (Proxy @a) arg) v tm

subst :: forall a b. (SupportedPrim a, SupportedPrim b) => TermSymbol -> Term a -> Term b -> Term b
subst sym@(TermSymbol (_ :: Proxy c) _) term input = case eqT @c @a of
  Just Refl -> gov input
  Nothing -> error "Bad symbol type"
  where
    gov :: (SupportedPrim x) => Term x -> Term x
    gov b = case go (SomeTerm b) of
      SomeTerm v -> unsafeCoerce v
    go :: SomeTerm -> SomeTerm
    go = htmemo $ \stm@(SomeTerm (tm :: Term v)) ->
      case tm of
        ConcTerm _ cv -> case (R.typeRep :: R.TypeRep v) of
          R.App (R.App gf _) _ ->
            case R.eqTypeRep gf (R.typeRep @(-->)) of
              Just R.HRefl -> case cv of
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
        NotTerm _ op -> SomeTerm $ notb (gov op)
