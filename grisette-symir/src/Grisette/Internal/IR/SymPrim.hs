{-# LANGUAGE PatternSynonyms #-}

module Grisette.Internal.IR.SymPrim
  ( Union,
    UnaryOp (..),
    BinaryOp (..),
    TernaryOp (..),
    Term (..),
    introSupportedPrimConstraint,
    SomeTerm (..),
    SupportedPrim (..),
    castTerm,
    identity,
    identityWithTypeRep,
    pformat,
    constructUnary,
    constructBinary,
    constructTernary,
    concTerm,
    symbTerm,
    ssymbTerm,
    isymbTerm,
    sinfosymbTerm,
    iinfosymbTerm,
    termSize,
    termsSize,
    extractSymbolicsTerm,
    trueTerm,
    falseTerm,
    pattern BoolConcTerm,
    pattern TrueTerm,
    pattern FalseTerm,
    pattern BoolTerm,
    notb,
    eqterm,
    neterm,
    orb,
    andb,
    iteterm,
    implyb,
    xorb,
    unaryUnfoldOnce,
    binaryUnfoldOnce,
    pattern UnaryTermPatt,
    pattern BinaryTermPatt,
    pattern TernaryTermPatt,
    PartialFunc,
    PartialRuleUnary,
    TotalRuleUnary,
    PartialRuleBinary,
    TotalRuleBinary,
    totalize,
    totalize2,
    UnaryPartialStrategy (..),
    unaryPartial,
    BinaryCommPartialStrategy (..),
    BinaryPartialStrategy (..),
    binaryPartial,
    integerConcTermView,
    pattern IntegerConcTerm,
    pattern IntegerTerm,
    DivI (..),
    divi,
    pattern DivITerm,
    ModI (..),
    modi,
    pattern ModITerm,
    pattern NumConcTerm,
    pattern NumOrdConcTerm,
    AddNum (..),
    addNum,
    pattern AddNumTerm,
    minusNum,
    UMinusNum (..),
    uminusNum,
    pattern UMinusNumTerm,
    AbsNum (..),
    absNum,
    pattern AbsNumTerm,
    SignumNum (..),
    signumNum,
    pattern SignumNumTerm,
    TimesNum (..),
    timesNum,
    pattern TimesNumTerm,
    LTNum (..),
    ltNum,
    pattern LTNumTerm,
    LENum (..),
    leNum,
    pattern LENumTerm,
    gtNum,
    geNum,
    pattern TabularFuncConcTerm,
    pattern TabularFuncTerm,
    ApplyF (..),
    applyf,
    pattern ApplyFTerm,
  )
where

import Grisette.IR.SymPrim.Data.Prim.Bool
import Grisette.IR.SymPrim.Data.Prim.Helpers
import Grisette.IR.SymPrim.Data.Prim.Integer
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Grisette.IR.SymPrim.Data.Prim.Num
import Grisette.IR.SymPrim.Data.Prim.TabularFunc
import Grisette.IR.SymPrim.Data.Union
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.SomeTerm
