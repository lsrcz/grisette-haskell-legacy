{-# LANGUAGE PatternSynonyms #-}

module Grisette.Core
  ( -- * Note for the examples
    --
    -- | This module does not contain actual implementation for symbolic primitive types, and
    -- the examples in this module cannot be executed solely with @grisette-core@ package.
    -- They rely on the implementation in @grisette-symprim@ package.

    -- * Symbolic Operators
    SEq (..),
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

    -- * Symbolic Primitives
    PrimWrapper (..),
    pattern Conc,
    ExtractSymbolics (..),

    -- * UnionM Monad
    UnionMBase,
    IsConcrete,
    UnionOp (..),
    pattern SingleU,
    pattern GuardU,
    makeUnionMWrapper,
    makeUnionMWrapper',

    -- * Merging
    MergeStrategy (..),
    derivedMergeStrategy,
    wrapMergeStrategy,
    Mergeable (..),
    Mergeable1 (..),
    withMergeable,
    SimpleMergeable (..),
    SimpleMergeable1 (..),
    withSimpleMergeable,
    withSimpleMergeableU,
    UnionSimpleMergeable1 (..),
    withUnionSimpleMergeable,
    withUnionSimpleMergeableU,
    MonadUnion (..),
    getSingle,

    -- * Wrapped Monadic Combinators with Mergeable Knowledge Propagaion
    mrgFmap,
    mrgLift,
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgMsum,
    
    -- * Standard Errors
    AssertionError (..),
    VerificationConditions (..),
    ArithException (..),
    TransformError (..),
    gthrowError,
    gassertWithError,
    gassert,
    gassume,

    -- * Symbolic Generation
    -- ** Symbolic Generation Context
    GenSymIndex (..),
    GenSymIdent,
    pattern GenSymIdent,
    name,
    nameWithInfo,
    FileLocation (..),
    nameWithLoc,

    -- ** Symbolic Generation Monad
    GenSymFresh,
    GenSymFreshT,
    runGenSymFresh,
    runGenSymFreshT,

    -- ** Symbolic Generation Class
    GenSym (..),
    GenSymSimple (..),
    genSym,
    genSymSimple,

    -- ** Symbolic Generation Class Derivation
    derivedNoSpecGenSymFresh,
    derivedNoSpecGenSymSimpleFresh,
    derivedSameShapeGenSymSimpleFresh,

    -- ** Symbolic choice
    choose,
    simpleChoose,
    chooseU,

    -- ** Useful specifications
    NumGenBound(..),
    NumGenUpperBound(..),
    ListSpec (..),
    SimpleListSpec (..),

    -- * Evaluation and Conversion between Concrete and Symbolic values
    Evaluate (..),
    evaluateToCon,
    ToCon (..),
    ToSym (..),
  
    -- * Memoization
    MemoHashMap (..),
    emptyMemoHashMap,
    enum',
    htmemo,
    htmemo2,
    htmemo3,
    htmup,
    htmemoFix,

    -- * Bundled Constructor Wrappers
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

    -- * Type Class Derivation
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
