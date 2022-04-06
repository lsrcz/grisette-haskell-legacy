{-# LANGUAGE PatternSynonyms #-}

module Grisette.Core
  ( SEq (..),
    LogicalOp (..),
    SymBoolOp,
    ITEOp (..),
    BVConcat (..),
    BVExtend (..),
    BVSelect (..),
    bvextract,
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
    gassert,
    ExtractSymbolics (..),
    MergeStrategy (..),
    derivedMergeStrategy,
    wrapMergeStrategy,
    Mergeable (..),
    Mergeable1 (..),
    withMergeable,
    PrimWrapper (..),
    pattern Conc,
    MonadUnion (..),
    getSingle,
    SimpleMergeable (..),
    SimpleMergeable1 (..),
    UnionSimpleMergeable1 (..),
    withSimpleMergeable,
    withUnionSimpleMergeable,
    withSimpleMergeableU,
    withUnionSimpleMergeableU,
    SOrd (..),
    Evaluate (..),
    evaluateToCon,
    GenSymState,
    GenSymFresh,
    GenSymFreshT,
    runGenSymFresh,
    runGenSymFreshT,
    GenSym (..),
    GenSymSimple (..),
    genSym,
    genSymSimple,
    derivedNoSpecGenSymFresh,
    derivedNoSpecGenSymSimpleFresh,
    derivedSameShapeGenSymSimpleFresh,
    choose,
    simpleChoose,
    chooseU,
    NumGenBound(..),
    NumGenUpperBound(..),
    ListSpec (..),
    SimpleListSpec (..),
    ToCon (..),
    ToSym (..),
    mrgFmap,
    MemoHashMap (..),
    emptyMemoHashMap,
    enum',
    mrgLift,
    UnionMBase,
    IsConcrete,
    AssertionError (..),
    VerificationConditions (..),
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgMsum,
    UnionOp (..),
    pattern SingleU,
    pattern GuardU,
    makeUnionMWrapper,
    makeUnionMWrapper',
    uTrue,
    uFalse,
    uunit,
    uTuple2,
    uTuple3,
    uJust,
    uNothing,
    uLeft,
    uRight,
    uInL,
    uInR,
    uAssertionViolation,
    uAssumptionViolation,
    htmemo,
    htmemo2,
    htmemo3,
    htmup,
    htmemoFix,
    Default(..),
  )
where

import Generics.Deriving (Default(..))
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
import Grisette.Data.Class.Evaluate
import Grisette.Data.Class.GenSym
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.UnionOp
import Grisette.Data.MemoUtils
import Grisette.TH
import Grisette.BuiltinUnionMWrappers
import Grisette.Data.Class.BitVector
