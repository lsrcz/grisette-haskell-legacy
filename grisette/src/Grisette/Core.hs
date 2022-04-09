{-# LANGUAGE PatternSynonyms #-}

module Grisette.Core
  ( SEq (..),
    SOrd (..),
    LogicalOp (..),
    SymBoolOp,
    ITEOp (..),
    BVConcat (..),
    BVExtend (..),
    BVSelect (..),
    bvextract,
    SignedDivMod (..),
    UnsignedDivMod (..),
    SignedQuotRem (..),
    SymIntegerOp,
    Function (..),
    (#~),

    AssertionError (..),
    VerificationConditions (..),
    ArithException (..),
    TransformError (..),
    gthrowError,
    gassertWithError,
    gassert,

    MergeStrategy (..),
    derivedMergeStrategy,
    wrapMergeStrategy,
    Mergeable (..),
    Mergeable1 (..),
    withMergeable,
    SimpleMergeable (..),
    SimpleMergeable1 (..),
    UnionSimpleMergeable1 (..),
    withSimpleMergeable,
    withUnionSimpleMergeable,
    withSimpleMergeableU,
    withUnionSimpleMergeableU,
    MonadUnion (..),
    getSingle,

    ExtractSymbolics (..),
    PrimWrapper (..),
    pattern Conc,

    GenSymIndex (..),
    GenSymIdent,
    pattern GenSymIdent,
    name,
    nameWithInfo,
    FileLocation (..),
    nameWithLoc,
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

    Evaluate (..),
    evaluateToCon,
    ToCon (..),
    ToSym (..),

    
    mrgFmap,
    mrgLift,
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgMsum,

    UnionMBase,
    IsConcrete,
    UnionOp (..),
    pattern SingleU,
    pattern GuardU,
    makeUnionMWrapper,
    makeUnionMWrapper',

    MemoHashMap (..),
    emptyMemoHashMap,
    enum',
    htmemo,
    htmemo2,
    htmemo3,
    htmup,
    htmemoFix,

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
