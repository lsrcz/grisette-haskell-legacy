{-# LANGUAGE PatternSynonyms #-}

module Grisette.Core
  ( -- * Note for the examples
    --
    -- | This module does not contain actual implementation for symbolic primitive types, and
    -- the examples in this module cannot be executed solely with @grisette-core@ package.
    -- They rely on the implementation in @grisette-symprim@ package.

    -- * Symbolic Operators
    -- | #symop#
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
    slocsymb,
    ilocsymb,
    ExtractSymbolics (..),

    -- * UnionM Monad
    UnionMBase,
    IsConcrete,
    UnionOp (..),
    UnionPrjOp (..),
    pattern SingleU,
    pattern GuardU,
    makeUnionMWrapper,
    makeUnionMWrapper',
    liftToMonadUnion,

    -- * Merging
    MergeStrategy (..),
    derivedMergeStrategy,
    wrapMergeStrategy,
    wrapMergeStrategy2,
    Mergeable (..),
    Mergeable1 (..),
    Mergeable2 (..),
    mergeStrategy1,
    mergeStrategy2,
    DynamicOrderedIdx (..),
    StrategyList (..),
    buildStrategyList,
    resolveStrategy,
    resolveStrategy',

    -- withMergeable,
    SimpleMergeable (..),
    SimpleMergeable1 (..),
    mrgIte1,
    SimpleMergeable2 (..),
    mrgIte2,
    -- withSimpleMergeable,
    -- withSimpleMergeableU,
    UnionMergeable1 (..),
    mrgIf,
    merge,
    -- withUnionSimpleMergeable,
    -- withUnionSimpleMergeableU,
    MonadUnion,
    getSingle,
    mrgReturnWithStrategy,
    mrgBindWithStrategy,
    mrgReturn,
    (>>=~),

    -- * Wrapped Monadic Combinators with Mergeable Knowledge Propagaion
    mrgFoldM,
    (>>~),
    mrgMzero,
    mrgMplus,
    mrgFmap,

    mrgFoldlM,
    mrgFoldrM,
    mrgTraverse_,
    mrgFor_,
    mrgMapM_,
    mrgForM_,
    mrgSequence_,
    mrgMsum,

    mrgTraverse,
    mrgSequenceA,
    mrgFor,
    mrgMapM,
    mrgForM,
    mrgSequence,

    mrgLift,
    mrgThrowError,
    mrgCatchError,
    
    -- * Standard Errors
    -- | #errors#
    AssertionError (..),
    VerificationConditions (..),
    ArithException (..),
    TransformError (..),
    symAssert,
    symAssume,
    symFailIfNot,
    symThrowTransformableError,

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
    EnumGenBound(..),
    EnumGenUpperBound(..),
    ListSpec (..),
    SimpleListSpec (..),

    -- * Evaluation and Conversion between Concrete and Symbolic values
    Evaluate (..),
    evaluateToCon,
    ToCon (..),
    ToSym (..),

    -- * Solver interface
    SolverErrorTranslation (..),
    SolverTranslation (..),
    CegisErrorTranslation (..),
    CegisTranslation (..),
    Solver (..),
    SolveProblem
      ( Formula,
        WithExcept,
        ArgFormula,
        ArgWithExcept
      ),
    solve,
    CegisProblem
      ( CFormulaPair,
        CArgFormulaPair,
        CForallFormulaPair,
        CArgForallFormulaPair,
        CWithExcept,
        CArgWithExcept,
        CForallWithExcept,
        CArgForallWithExcept
      ),
    cegis,
    forallIn,
    argBy,
    forallBy,
    translateBy,
  
    -- * Memoization
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
    Default1(..),
  )
where

import Generics.Deriving (Default(..), Default1(..))
import Grisette.Control.Exception
import Grisette.Control.Monad
import Grisette.Control.Monad.Except
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
import Grisette.Data.FileLocation
import Grisette.Data.MemoUtils
import Grisette.TH
import Grisette.BuiltinUnionMWrappers
import Grisette.Data.Class.BitVector
import Grisette.Data.Class.Solver
import Grisette.Control.Monad.Union
import Grisette.Data.Foldable
import Grisette.Data.Traversable
