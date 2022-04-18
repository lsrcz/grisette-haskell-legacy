module Grisette.Tutorial.Essentials.Essentials (
  -- * Preface
  -- | Grisette is a monadic symbolic compilation library.
  -- It allows the programmers to conveniently and efficiently
  -- reason about program behaviors with constraint solvers.
  -- 
  -- The core of Grisette is a monadic container 'UnionM' that represents __multi-path executions__.
  -- It can easily be composed with the existing monadic programming infrastructures to get
  -- error handling, stateful programming, or monadic coroutines in the multi-path execution scenario.
  --
  -- To perform symbolic compilation, Grisette provides the support of __symbolic values__. 
  -- The primitive values are supported with a symbolic intermediate representation,
  -- which is very similar to SMT formulas.
  -- The values with complex types and representations are supported with the 'UnionM' container,
  -- which will do state merging to avoid path explosion.
  -- 
  -- Another useful concept in symbolic compilation is __error handling__.
  -- In Grisette, the user can not only perform symbolic compilation with the traditional assertions / assumptions,
  -- but also can use any user-defined error types to express the desired program behaviors.
  -- Grisette also provides handy constructs to translate the symbolic compilation results to solver queries.
  --
  -- Grisette is extensible. Grisette provides a set of handy type classes that are useful in
  -- constructing a real world tool.
  -- The user can easily work with user-defined data structures by implementing some of the type classes.
  --
  -- This chapter describes the essentials of solver-aided programming in Grisette.
  -- We will also provide comparisons to the related concepts in Rosette for the Rosette users.
  
  -- * Symbolic primitive values
  -- ** Creation
  -- | In Grisette, we have two kinds of the primitive types: concrete and symbolic.
  -- Concrete primitive types are plain Haskell primitive types, e.g. 'Integer' or 'Bool'.
  -- These types do not have the ability to represent values with symbolic holes to be filled in by the solver.
  -- For example, in the following (pseudo-)code, @a@ represents a symbolic hole, and @ite a 0 1@ is a symbolic
  -- integer value with a symbolic hole.
  --
  -- > 0         -- representable by Integer type
  -- > 1         -- representable by Integer type
  -- > ite a 0 1 -- not representable by Integer type
  --
  -- Here the symbolic hole is a placeholder for concrete values,
  -- and the constraint solver is able to fill in the symbolic holes with concrete values.
  -- For example, we can ask the solver what the value @a@ should be to make @ite a 0 1@ equals to 1, and the solver
  -- will be able to figure out that @a@ should be 'False'. 
  --
  -- To represent the symbolic values, a symbolic type is needed.
  -- Grisette allows the users to define their own symbolic
  -- primitive types, but for most cases, the user can rely on the default implementation shipped with Grisette.
  --
  -- In the default implementation, the symbolic primitive types are represented with 'Sym'.
  -- For example, the symbolic boolean type is 'Sym Bool', and the symbolic integer type is 'Sym Integer'.
  -- The 'Sym' type is capable to represent concrete values, symbolic holes, and symbolic formulas constructed with them.
  --
  -- For concrete values, the user can easily wrap them into 'Sym':
  --
  -- >>> conc False :: Sym Bool
  -- false
  -- >>> conc 1 :: Sym Integer
  -- 1I
  --
  -- Symbolic integers can also be constructed from integer literals:
  --
  -- >>> 1 :: Sym Integer
  -- 1I
  --
  -- The symbolic holes are named in Grisette.
  -- They can be constructed with functions defined in the 'PrimWrapper' class.
  --
  -- Simply-named and indexed symbolic holes:
  --
  -- >>> ssymb "a" :: Sym Integer -- Simple-named symbolic holes
  -- a
  -- >>> isymb 1 "a" :: Sym Integer -- Indexed symbolic holes
  -- a@1
  -- 
  -- Additional information can be attached to further distinguish the holes:
  --
  -- >>> sinfosymb "a" True :: Sym Integer
  -- a:True
  -- >>> isinfosymb 1 "a" (2 :: Integer) :: Sym Integer
  -- a@1:2
  --
  -- Note that the holes are global in the whole program, that is,
  -- two holes with the same type, name, index, extra information are always the same.
  -- (The '==' in the following code won't do symbolic equality check, it only checks if the two symbolic values
  -- are identical).
  --
  -- >>> (ssymb "a" :: SymInteger) == (ssymb "a" :: SymInteger)
  -- True
  --
  -- To reduce the burden on the programmers to choose unique names, we provided the following Template Haskell
  -- construct to bundle the current file location as the extra information.
  -- 'slocsymb' and 'ilocsymb' are similar to 'ssymb' and 'isymb', respectively.
  -- 
  -- >>> $$(slocsymb "a") :: SymInteger
  -- a:<interactive>:13:4-15
  -- >>> $$(ilocsymb 1 "a") :: SymInteger
  -- a@1:<interactive>:14:4-17
  -- 
  -- Grisette also supports generating \"fresh\" symbolic variables within a monadic environment.
  -- We will discuss this in the section [Generating symbolic values](#gensym).
  
  -- *** Note for Rosette users
  -- | The 'slocsymb' and 'ilocsymb' is similar to the @define-symbolic@ (without *) form in Rosette.
  --
  -- >>> $$(slocsymb "a") == $$(slocsymb "a")
  -- False
  -- >>> let static = $$(slocsymb "a")
  -- >>> static == static
  -- True
  --
  -- There's no @define-symbolic*@ equivalent in Grisette as it is not pure.
  -- However, in the section [Generating symbolic values](#gensym), we will discuss how to
  -- achieve a similar functionality with monads.

  -- ** Symbolic operations
  -- | In the last section, we used `==` to determine if two symbolic values are equal,
  -- and the result has the type 'Bool'.
  -- As we cannot represent the result of symbolic equivalence test, which is a symbolic value,
  -- with the concrete type 'Bool',
  -- the '==' operation, obviously, is concrete, and is not performing symbolic equivalence test.
  -- This requires us to implement a custom equivalence operator that has the symbolic equivalence semantics,
  -- and return a symbolic boolean value.
  --
  -- In Grisette, the symbolic equivalence relation is captured by the 'SEq' type class,
  -- and we can use the member function '==~' to test equivalence symbolically.
  -- Note that the @~@ postfix is usually used for symbolic operators.
  --
  -- >>> (ssymb "a" :: SymInteger) ==~ (ssymb "b") :: SymBool
  -- (== a b)
  --
  -- For some type classes, for example, 'Num', the standard library versions are reused because
  -- they have compatible type signatures.
  --
  -- >>> (ssymb "a" :: SymInteger) + ssymb "b"
  -- (+ a b)
  -- 
  -- More operators are available in Grisette, see the documentation at "Grisette.Core#symop" for details.

  -- *** Note for Rosette users
  -- | Rosette is weakly typed language, and it reuses and lifts the Racket library function with symbolic semantics.
  -- This is different from our settings.

  -- * UnionM monad, general symbolic types and multi-path execution 
  
  -- ** UnionM monad and general symbolic types
  -- | 'UnionM' is a monadic container with multi-path execution semantics encoded.
  -- The purpose of introducing 'UnionM' into the system is to provide a general way
  -- to represent complex symbolic types.
  -- Instead of defining symbolic types for each complex types, e.g.,
  -- in [sbv](https://hackage.haskell.org/package/sbv),
  -- 'SMaybe' is defined for symbolic optional values,
  -- and 'SEither' is defined for symbolic sums,
  -- we choose to represent such types directly by the concrete version guarded by
  -- path conditions, i.e., @(ite path-cond1 value1 (ite path-cond2 value2 value3))@.
  -- The downside of this approach is that the values need to be finitized,
  -- e.g., @sbv@'s 'SList' represents a list of __possibly arbitrary__ but finite length,
  -- while with our encoding, the possible lengths need to be explicitly encoded.
  -- The upside of our approach is its generality, and
  -- we don't have to define dedicate symbolic types and define their translations
  -- to underlying constraint solvers.
  --
  -- Take symbolic optional boolean as an example.
  -- In Grisette, a symbolic optional boolean is represented with the type @UnionM (Maybe (Sym Bool))@.
  -- The type wrapped in the 'UnionM', which is @Maybe (Sym Bool)@, is an optional value for symbolic boolean.
  -- wrapping this type with 'UnionM' enables the solver to choose from 'Nothing' or 'Just'.
  --
  -- As 'UnionM' is a monad, we can use 'return' to wrap a value in it.
  -- However, we recommend to __/always/__ use the specialized version 'mrgReturn' instead
  -- unless you understand what Grisette would do.
  -- This is related to how we perform the state merging in Grisette, and will be elaborated later
  -- in the [Merge Strategy](#merge) section.
  -- In short, the 'UnionM' with state merging is in fact a constrained monad and we cannot maintain
  -- the 'Mergeable' constraint with the standard monadic combinators.
  -- We (partially) overcome this problem by capturing and propagate the constraint within
  -- 'UnionM', and 'mrgReturn' can resolve and capture the constraint.
  --
  -- >>> return Nothing :: UnionM (Maybe (Sym Bool))
  -- UAny (Single Nothing)
  -- >>> mrgReturn Nothing :: UnionM (Maybe (Sym Bool))
  -- UMrg (Single Nothing)
  -- >>> return $ Just $ ssymb "a" :: UnionM (Maybe (Sym Bool))
  -- UAny (Single (Just a))
  -- >>> mrgReturn $ Just $ ssymb "a" :: UnionM (Maybe (Sym Bool))
  -- UMrg (Single (Just a))
  --
  -- To allow the solver to choose from different branches, 'mrgIf' is handy.
  -- 
  -- >>> mrgIf (ssymb "a") (mrgReturn Nothing) (mrgReturn $ Just $ ssymb "b")
  -- UMrg (Guard a (Single Nothing) (Single (Just b)))

  -- ** Multi-path execution

  -- ** Using monad transformers
  
  -- * Error handling and solver queries

  -- * Supportive type classes

  -- ** Symbolic equality and ordering

  -- ** Conversion between symbolic and concrete types

  -- ** Merge strategy
  -- | #merge#

  -- ** Generating symbolic values
  -- | #gensym#

  -- ** Symbolic hole extraction and evaluation
  

)where

import Grisette
import Data.SBV

