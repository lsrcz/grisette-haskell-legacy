{-# LANGUAGE PatternSynonyms #-}

module Grisette.Core
  ( SEq (..),
    (/=~),
    LogicalOp (..),
    SymBoolOp,
    ITEOp (..),
    ArithException (..),
    SignedDivMod (..),
    UnsignedDivMod (..),
    SignedQuotRem (..),
    SymIntegerOp,
    Function (..),
    (#~),
    TransformError (..),
    gthrowError,
    gassertWithError,
    ExtractSymbolics (..),
    MergeStrategy (..),
    derivedMergeStrategy,
    wrapMergeStrategy,
    Mergeable (..),
    Mergeable1 (..),
    withMergeable,
    PrimWrapper (..),
    pattern Conc,
    UnionMOp (..),
    getSingle,
    SimpleMergeable (..),
    SimpleMergeable1 (..),
    withSimpleMergeable,
    withUnionMSimpleMergeable,
    withSimpleMergeableU,
    withUnionMSimpleMergeableU,
    SOrd (..),
    derivedSymLt,
    derivedSymLe,
    derivedSymGt,
    derivedSymGe,
    SymEval (..),
    symevalToCon,
    SymGenState,
    SymGen (..),
    genSym,
    SymGenSimple (..),
    genSymSimple,
    SymGenNoSpec (..),
    SymGenSimpleNoSpec (..),
    genSymIndexedWithDerivedNoSpec,
    genSymSimpleIndexedWithDerivedNoSpec,
    genSymIndexedWithDerivedSameShape,
    choose,
    simpleChoose,
    chooseU,
    runSymGenIndexed,
    ListSpec (..),
    SimpleListSpec (..),
    ToCon (..),
    ToSym (..),
    mrgFmap,
    MemoHashMap (..),
    emptyMemoHashMap,
    mrgLift,
    UnionMBase,
    AssertionError (..),
    VerificationConditions (..),
    mrgReturn,
    (>>=~),
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgMsum,
    UnionOp (..),
    pattern SingleU,
    pattern GuardU,
  )
where

import Grisette.Control.Exception
import Grisette.Control.Monad
import Grisette.Control.Monad.Trans
import Grisette.Control.Monad.UnionMBase
import Grisette.Data.Class.Bool
import Grisette.Data.Class.Error
import Grisette.Data.Class.ExtractSymbolics
import Grisette.Data.Class.Function
import Grisette.Data.Class.Integer
import Grisette.Data.Class.Mergeable
import Grisette.Data.Class.OrphanGeneric ()
import Grisette.Data.Class.PrimWrapper
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.SymEval
import Grisette.Data.Class.SymGen
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.UnionOp
import Grisette.Data.Functor
import Grisette.Data.MemoUtils
