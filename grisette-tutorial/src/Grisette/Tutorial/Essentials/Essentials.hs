{-# OPTIONS_GHC -Wno-unused-imports #-}

module Grisette.Tutorial.Essentials.Essentials (
  -- * Preface
  -- | Grisette is a monadic symbolic compilation library.
  -- It allows the programmers to conveniently and efficiently
  -- reason about program behaviors with constraint solvers.
  --
  -- There are already some existing symbolic reasoning libraries
  -- in haskell, for example, [sbv](https://hackage.haskell.org/package/sbv),
  -- [z3](https://hackage.haskell.org/package/z3) or [what4](https://hackage.haskell.org/package/what4).
  -- Compared to them, Grisette is a higher-level tool.
  -- In addition to building and representing symbolic values and constraints,
  -- Grisette has builtin support to track symbolic path conditions and errors for
  -- symbolic compiling and reasoning about programs.
  --
  -- [Rosette](https://emina.github.io/rosette/) is another high-level programming language
  -- for reasoning about programs.
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
  -- These types can onl represent concrete values, and
  -- do not have the ability to represent symbolic formulas.
  -- For example, in the following (pseudo-)code, @a@ represents a __symbolic constant__,
  -- and @ite a 0 1@ is a symbolic
  -- integer value with a symbolic constant.
  --
  -- > 0         -- representable by Integer type
  -- > 1         -- representable by Integer type
  -- > ite a 0 1 -- not representable by Integer type
  --
  -- Here the term __symbolic constant__ comes from SMT language.
  -- They are placeholders for concrete values,
  -- and the constraint solver is able to figure out which concrete value a given symbolic
  -- constant represents.
  -- For example, we can ask the solver what the value @a@ should be to make @ite a 0 1@ equals to 1,
  -- and the solver will be able to figure out that @a@ should be 'False'. 
  --
  -- To represent the symbolic values, we need to introduce symbolic primitive types.
  -- Grisette allows the users to define their own symbolic
  -- primitive types, but for most cases, the user can rely on the default implementation shipped with Grisette.
  -- In the default implementation, the symbolic primitive types are represented with 'Sym'.
  -- For example, the symbolic boolean type is @Sym Bool@, and the symbolic integer type is @Sym Integer@.
  -- The 'Sym' type is capable to represent concrete values, symbolic constants,
  -- and symbolic formulas constructed with them.
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
  -- The symbolic constants are named in Grisette.
  -- They can be constructed with functions defined in the 'PrimWrapper' class.
  -- The simplest way to construct a symbolic constant is to use the 'ssymb',
  -- which means \"Simple symbol\".
  --
  -- >>> ssymb "a" :: Sym Integer -- Simply-named symbolic constants
  -- a
  --
  -- Note that the constants are global in the whole program, that is,
  -- two constants with the same name are always the same,
  -- and will always be assigned with the same concrete constants by the constraint solver.
  -- (The '==' in the following code won't do symbolic equality check,
  -- it only checks if the two symbolic formulas are identical).
  --
  -- >>> (ssymb "a" :: Sym Integer) == (ssymb "a" :: Sym Integer)
  -- True
  --
  -- With @-XOverloadedStrings@ extension,
  -- you can directly use string literals to create simply-named symbolic constants.
  -- 
  -- >>> "a" :: Sym Integer
  -- a
  -- 
  -- To reduce the burden on the programmers to choose unique names, we provided the following Template Haskell
  -- construct to bundle the current file location as the extra information.
  -- 'slocsymb' means \"Simple symbol with location\".
  -- Calling 'slocsymb' in different locations will result in different symbolic constants,
  -- but calling 'slocsymb' multiple time in the same location will return the same symbolic constant.
  -- 
  -- >>> $$(slocsymb "a") :: SymInteger -- sample output: a:<interactive>:13:4-15
  -- a:<interactive>:...
  -- >>> ($$(slocsymb "a") :: SymBool) == $$(slocsymb "a")
  -- False
  -- >>> let static1 = \_ -> $$(slocsymb "a") :: SymBool
  -- >>> let static2 = \_ -> $$(slocsymb "a") :: SymBool
  -- >>> static1 () == static2 ()
  -- False
  -- >>> static1 () == static1 ()
  -- True
  -- 
  -- Grisette also supports generating \"fresh\" symbolic variables within a monadic environment.
  -- We will discuss this in the section [Generating symbolic values](#gensym).
  
  -- *** Note for Rosette users
  -- | The 'slocsymb' is similar to the @define-symbolic@ (without *) form in Rosette.
  -- In Rosette, you can define symbolic variables as follows.
  -- It ensures that each @define-symbolic@ call defines a unique symbolic constant,
  -- but each call to the same @define-symbolic@ returns the same symbolic constant.
  --
  -- The following code in Rosette is equivalent to the previous 'slocsymb' examples.
  --
  -- >(define (static1)
  -- >  (define-symbolic a boolean?)
  -- >  a)
  -- >(define (static2)
  -- >  (define-symbolic a boolean?)
  -- >  a)
  -- >> (term=? (static1) (static1))
  -- >#t
  -- >> (term=? (static1) (static2))
  -- >#f
  --
  -- There's no @define-symbolic*@ equivalent in Grisette as it is not pure.
  -- However, in the section [Generating symbolic values](#gensym), we will discuss how to
  -- achieve a similar functionality with monads.

  -- ** Symbolic operations
  -- | In the last section, we used `==` to determine if two symbolic values are equal,
  -- and the result has the type 'Bool'.
  -- This operation is only comparing if the two symbolic value has the
  -- same representation, and will not performing symbolic equivalence test.
  --
  -- In Grisette, the symbolic equivalence relation is captured by the 'SEq' type class.
  -- The symbolic equivalence operator '==~' will test equivalence symbolically
  -- and construct symbolic formulas.
  -- The resulting formula can be solved by the constraint solver.
  --
  -- >>> ("a" :: SymInteger) ==~ "b" :: SymBool
  -- (== a b)
  --
  -- Note that the @~@ postfix is one of the naming conventions
  -- that is usually used for symbolic operators.
  --
  -- For some type classes, for example, 'Num', the standard library versions are reused because
  -- they have compatible type signatures.
  --
  -- >>> "a" + "b" :: SymInteger
  -- (+ a b)
  -- 
  -- More operators are available in Grisette, see the documentation at "Grisette.Core#symop" for details.

  -- *** Note for Rosette users
  -- | Rosette is weakly typed language, and it reuses and lifts the Racket library function with symbolic semantics.
  -- This is different from our settings.
  -- For example, the @eq?@ operator will test equivalence symbolically.
  --
  -- >> (define-symbolic a b integer?)
  -- >> (eq? a b)
  -- >(= a b)
  --
  -- @term=?@ tests if two terms has the same representation, but it is rarely used.

  -- * UnionM monad, general symbolic types and multi-path execution 
  
  -- ** UnionM container and general symbolic types
  -- | 'UnionM' is a container with multi-path execution semantics encoded.
  -- The purpose of introducing 'UnionM' into the system is to provide a general way
  -- to represent complex symbolic types.
  -- Instead of defining symbolic types for each complex types, e.g.,
  -- in [sbv](https://hackage.haskell.org/package/sbv),
  -- 'SMaybe' is defined for symbolic optional values,
  -- and 'SEither' is defined for symbolic sums,
  -- we choose to represent such types directly by path-condition-guarded concrete values,
  -- i.e., @(If path-cond1 value1 (If path-cond2 value2 value3))@.
  -- The @If@ here has the if-then-else semantics,
  -- which means,
  -- if @path-cond1@ is true under some assignment to the symbolic constants,
  -- then the value should be @value1@ with the assignment to the symbolic constants,
  -- or we should look at the other branch @(If path-cond2 value2 value3)@.
  --
  -- The values contained in the 'UnionM' will be merged when possible to mitigate
  -- the notorious path-explosion problem in symbolic compilation.
  -- This merging algorithm is key to Grisette's efficient symbolic compilation.
  -- We will mention this many times without describing it,
  -- and then we will discuss it in detail later.

  -- *** Tradeoffs
  -- | There are tradeoffs to use this representation.
  --
  -- The advantage of our approach is its generality.
  -- With our approach,
  -- a new type can be easily supported, and
  -- there's no need to define dedicated symbolic primitive types
  -- and their translations to underlying constraint solvers.
  -- Take symbolic lists as an example.
  -- In Grisette, a symbolic list of symbolic booleans is represented with the type @UnionM [Sym Bool]@.
  -- The type wrapped in the 'UnionM', which is @[Sym Bool]@, is an concrete list for symbolic booleans.
  -- Wrapping this type with 'UnionM' enables the solver to choose from a set of lists.
  -- For example, @(If a [b] [c,d])@ is a union of symbolic boolean lists that contains
  -- either one or two values.
  --
  -- The reason why our approach can support arbitrary type without defining their translations
  -- is partial evaluation.
  -- As the values wrapped in the 'UnionM' are concrete,
  -- we can apply the concrete functions from Haskell's standard library
  -- on them, and the complex types will be evaluated away.
  -- For example, to take the first element symbolically from
  -- @(If a [b] [c,d])@, what we need is just to apply the 'head' function to each concrete list value,
  -- and we will get @(If a b c)@. This will be merged to a single symbolic formula
  -- @(ite a b c)@ (we will discuss the merging later), which is free of the list type,
  -- and can be easily translated to the constraint solver.
  --
  -- The downside of our approach is that the values need to be finitized,
  -- e.g., @sbv@'s 'SList' represents a list of __possibly arbitrary__ but finite length.
  -- You can directly declare a symbolic constant for symbolic lists
  -- with __unbounded length__ in [sbv](https://hackage.haskell.org/package/sbv),
  -- and let the solver figure it out.
  -- The following example comes from [sbv](https://hackage.haskell.org/package/sbv)'s documentation,
  -- the first line declares a symbolic list constant, which has unbounded length,
  -- and the third line constrains the length.
  -- The 'Data.SBV..==' operator is for symbolic equality.
  --
  -- > do fibs <- sList "fibs"
  -- >    -- constrain the length
  -- >    constrain $ L.length fibs .== 200
  -- >    -- Constrain first two elements
  -- >    constrain $ fibs .!! 0 .== 1
  -- >    constrain $ fibs .!! 1 .== 1
  -- >    -- Constrain an arbitrary element at index `i`
  -- >    let constr i = constrain $ fibs .!! i + fibs .!! (i+1) .== fibs .!! (i+2)
  -- >    -- Constrain the remaining elts
  -- >    mapM_ (constr . fromIntegral) [(0::Int) .. 197]
  --
  -- While with our encoding,
  -- the possible lengths need to be explicitly encoded in each concrete branch,
  -- thus we can only perform bounded reasoning.
  -- However, if the user needs unbounded lists,
  -- he can implement his own symbolic primitive types with lists as a primitive,
  -- and design his own translation to the solvers.
  -- This could possibly be more efficient as modern solvers
  -- support reasoning with ADTs.
  -- Grisette does not have native support for this at this time.

  -- *** User defined ADTs
  -- | The following code defines a simple symbolic arithmetic expression syntax tree.
  --
  -- >>> :{
  --   data Expr
  --     = IntegerConst SymInteger
  --     | Plus (UnionM Expr) (UnionM Expr)
  --     | Minus (UnionM Expr) (UnionM Expr)
  --     deriving (Generic)
  --     deriving (Mergeable SymBool) via (Default Expr)
  -- :}
  -- 
  -- The field declarations are worth noting here.
  -- For the @IntegerConst@ branch, the field is declared as 'SymInteger',
  -- which is a type synonym of @Sym Integer@.
  -- For the @Plus@ and @Minus@ branch,
  -- the fields are declared as @Expr@ wrapped in the 'UnionM' container.
  -- An alternative implementation would be directly use 'Expr' as the fields,
  -- and Grisette __will__ work with that with the default derived 'Mergeable' instance,
  -- but the values will be merged differently.
  --
  -- Controlling how Grisette merges things is an advanced topic,
  -- and may affect the performance dramatically.
  -- Generally, for most data types, you can use symbolic primitives
  -- directly for the primitive fields, and use 'UnionM'-wrapped type for the
  -- fields with complex data, and you can get good performance.

  -- *** Note for Rosette users
  -- | Rosette has unions too, and Rosette's union is also representing a set of
  -- values to be chosen by the solver under some path conditions.
  -- A symbolic list wrapped in Rosette is also represented with a union.
  -- 
  -- >> (if a (list b) (list c d))
  -- >(union [a (b)] [(! a) (c d)])
  --
  -- The difference between Rosette's union and Grisette's 'UnionM' is mostly
  -- in the internal representation and merging algorithms,
  -- and the user usually does not have to care about it.
  -- For more details, please refer to the research paper TODO.........

  -- ** Multi-path execution and 'UnionM' monad

  -- *** Basic operations
  -- | Similar to the list monad, which represents nondeterministic computations,
  -- the 'UnionM' container is also a monad, and it models multi-path execution
  -- with path conditions maintained.
  --
  -- The 'return' function for 'UnionM' simply wraps a single value in 'UnionM',
  -- without any path conditions.
  -- It represents a single unconditional program execution path.
  -- We will explain what 'UAny' means later, and now you can focus on the structure
  -- wrapped in it only.
  --
  -- >>> return Nothing :: UnionM (Maybe (Sym Bool))
  -- UAny (Single Nothing)
  -- >>> return $ Just "a" :: UnionM (Maybe (Sym Bool))
  -- UAny (Single (Just a))
  --
  -- Before introducing the bind operator, we will take a look at 'UnionM'\'s
  -- 'mrgIf' operation to build multi-path execution.
  -- The 'mrgIf' has the similar semantics as the @if@ statement, but works symbolically.
  -- Instead of being evaluated to a single value chosen from then or else branch,
  -- it will maintain all the two branches,
  -- and place them under a 'If' with the path conditions.
  -- The solver will be able to assign concrete constants to the symbolic constants
  -- in the path condition thus choose from one of the branches.
  -- In the following example, if @a@ is assigned to @True@,
  -- the concrete value of the expression will be @Nothing@, or it will be @Just b@ with @b@
  -- assigned by the solver.
  --
  -- >>> -- if a then Nothing else Just b
  -- >>> mrgIf "a" (return Nothing) (return $ Just "b") :: UnionM (Maybe SymBool)
  -- UMrg (If a (Single Nothing) (Single (Just b)))
  --
  -- The bind function for 'UnionM' captures the semantics for sequential programs
  -- in multi-path execution.
  -- It pulls out the values from each branch in the 'UnionM',
  -- and run another multi-path computation on them under the corresponding path-condition.
  --
  -- For example,
  --
  -- >>> let l1 = mrgIf "a" (return ["b"]) (return ["c", "d"]) :: UnionM [SymBool]
  -- >>> let l2 = mrgIf "e" (return ["f"]) (return ["g", "h"])
  -- >>> :{
  --   -- l1 = if a then [b] else [c,d]
  --   -- l2 = if e then [f] else [g,h]
  --   -- l1 ++ l2
  --   do v1 <- l1 
  --      v2 <- l2
  --      return $ v1 ++ v2
  -- :}
  -- UAny (If a (If e (Single [b,f]) (Single [b,g,h])) (If e (Single [c,d,f]) (Single [c,d,g,h])))
  --
  -- You can see the path condition is correctly maintained in the result,
  -- that is, when @a@ is true and @e@ is true, the result would be @[b,f]@, etc.

  -- *** Knowledge propagation

  -- | In the last section, you may notice that some 'UnionM' are constructed with @UAny@,
  -- and some are constructed with @UMrg@.
  -- You may also notice that the sequential program in the last section results in
  -- four branches, and will grow exponentially when the program grows longer.
  --
  -- To solve this problem, Grisette features a merging algorithm for the values.
  -- Grisette provided a function called 'merge', which can be called on a 'UnionM'
  -- to merge the values.
  -- If we call the 'merge' function on the sequential program shown before,
  -- the two lists with the same length will be merged,
  -- and there will be only 3 branches in the result.
  --
  -- >>> let l1 = mrgIf "a" (return ["b"]) (return ["c", "d"]) :: UnionM [SymBool]
  -- >>> let l2 = mrgIf "e" (return ["f"]) (return ["g", "h"])
  -- >>> :{
  --   merge $ do
  --      v1 <- l1
  --      v2 <- l2
  --      return $ v1 ++ v2
  -- :}
  -- UMrg (If (&& a e) (Single [b,f]) (If (|| a e) (Single [(ite a b c),(ite a g d),(ite a h f)]) (Single [c,d,g,h])))
  --
  -- However, it's easy to forget calling 'merge' every time when you write a do-block,
  -- and this may result in low efficiency in symbolic compilation.
  -- It's also very hard to fully integrate the merging algorithm in the '>>=' function,
  -- because the '>>=' function in a standard Monad instance cannot resolve the 'Mergeable' constraint.
  -- To mitigate the problem, we adopted a approach inspired by 
  -- [knowledge propagation](https://okmij.org/ftp/Haskell/set-monad.html#PE).
  -- The 'UnionM' structure will capture the 'Mergeable' constraint if possible in
  -- 'UMrg', which can be propagated and used for further merging.
  --
  -- It is not possible for the functions from the standard library to catch
  -- the 'Mergeable' constraint, so we have specialized version for them.
  -- We highly recommend that the user __always__ use our specialized version as a safe choice,
  -- rather than use the ones from the standard library,
  -- especially when they have no clear idea how Grisette handles the 'Mergeable' knowledge.
  -- For example, to wrap a single value in the 'UnionM' instance, we highly recommend
  -- that the user __always__ use 'mrgReturn' rather than 'return'.
  -- To map the values contained in 'UnionM',
  -- we recommend that the user __always__ use 'mrgFmap' rather than 
  -- the 'fmap'.
  --
  -- >>> return ["a"] :: UnionM [SymBool]
  -- UAny (Single [a])
  -- >>> mrgReturn ["a"] :: UnionM [SymBool]
  -- UMrg (Single [a])
  --
  -- One exception for the __always__ rule is '>>='.
  -- We guarantee that '>>=' can propagate the 'Mergeable' knowledge,
  -- thus the user can use do-blocks without the need to call 'merge' every time.
  -- In the following example, the 'mrgReturn' collects the 'Mergeable'
  -- constraints.
  -- This knowledge will be propagated by '>>=', and will be used to merge the final
  -- result.
  --
  -- >>> let l1 = mrgIf "a" (return ["b"]) (return ["c", "d"]) :: UnionM [SymBool]
  -- >>> let l2 = mrgIf "e" (return ["f"]) (return ["g", "h"])
  -- >>> :{
  --   do
  --      v1 <- l1
  --      v2 <- l2
  --      mrgReturn $ v1 ++ v2
  -- :}
  -- UMrg (If (&& a e) (Single [b,f]) (If (|| a e) (Single [(ite a b c),(ite a g d),(ite a h f)]) (Single [c,d,g,h])))
  --
  -- One great property of the knowledge propagation approach is that
  -- if you stick to the @mrg@ prefixed version
  -- in your function implementation,
  -- it would be safe to use all the custom functions for high performance symbolic compilation.
  --
  -- >>> let f cond hd lst = mrgIf cond (mrgReturn lst) (mrgReturn $ hd : lst)
  -- >>> :{
  --   do lst <- mrgIf "a" (mrgReturn []) (mrgReturn ["b"]) :: UnionM [SymBool]
  --      f "c" "d" lst
  -- :}
  -- UMrg (If (&& a c) (Single []) (If (|| a c) (Single [(ite a d b)]) (Single [d,b])))
  
  -- ** Using monad transformers
  -- | The Grisette framework is extensible because it fit perfectly into
  -- Haskell's monadic programming infrastructure.
  -- Grisette abstracts the monads that are capable for multi-path execution with
  -- the type class 'MonadUnion', which provides the 'merge', 'mrgReturn', 'mrgIf' and '>>=~'
  -- functions.
  -- The first three functions are discussed before, while the '>>=~' function is just
  -- '>>=' with 'Mergeable' knowledge captured.
  -- A monad transformer can be easily supported by implementing the type class.
  --
  -- > class (UnionSimpleMergeable1 bool u, Monad u) =>
  -- >        MonadUnion bool u | u -> bool where
  -- >    merge :: Mergeable bool a => u a -> u a
  -- >    mrgReturn :: Mergeable bool a => a -> u a
  -- >    mrgIf :: Mergeable bool a => bool -> u a -> u a -> u a
  -- >    (>>=~) :: Mergeable bool b => u a -> (a -> u b) -> u b
  -- >    {-# MINIMAL merge #-}
  --
  -- Grisette is battery included and provided instances for most of the \'standard\' monad
  -- transformers in [mtl](https://hackage.haskell.org/package/mtl).
  -- The user can enhance the multi-path execution with various different
  -- functionalities with them
  -- For example,
  -- to do stateful programming in multi-path settings,
  -- we can just apply 'StateT' onto the 'UnionM' monad.
  -- Here is a simple example:
  --
  -- >>> let add1 = modify (+1)
  -- >>> :{
  --   m :: StateT Integer UnionM ()
  --   m = do mrgIf "a" add1 $ return ()
  --          mrgIf "b" add1 $ return ()
  -- :}
  --
  -- >>> runStateT m 0
  -- UMrg (If (! (|| a b)) (Single ((),0)) (If (! (&& a b)) (Single ((),1)) (Single ((),2))))
  --
  -- The program works as expected. If @a@ and @b@ are both false, then the final state would be 0.
  -- If they are both true, then the final state would be 2. Or the final state would be 1.
  
  -- * Exception handling and solver queries
  
  -- ** Why exception handling in Grisette
  -- | Exception handling is very essential in solver-aided tools
  -- to describe the desired behavior of a program in an expressive way.
  -- Suppose that you have a function with some preconditions and you are going to verify its correctness.
  -- Without any exception handling mechanism, you have to manually construct the constraints.
  -- For such a small problem, it is not that hard,
  -- and you can easily figure out that we should use the logical connective /implies/ to connect the pre-conditions and post-conditions.
  -- However, when you are verifying a real-world system, with a lot of interleaving pre- and post-conditions,
  -- manually figuring out the dependencies could be hard and error-prone.
  --
  -- Grisette supports the exception handling mechanism to help reduce
  -- manual constraint building.
  -- The exception handling mechanism in Grisette is very similar to the ones in other languages,
  -- in which the exceptions can be handled, or will terminate the program execution.
  -- The only difference is that Grisette can handle exceptions symbolically.
  --
  -- For the same verification scenario, we can abstract the condition violations as different kind of exceptions.
  -- The pre-condition violations can be abstracted as assumption violation exceptions,
  -- and the post-conditions violations can be abstracted as assertion violation exceptions.
  -- Then the correctness condition could be expressed as /no assumption violation implies no assertion violation/,
  -- and we can use the solver to prove this by proving that /the program terminates with assertion violation/ is not satisfiable.
  --
  -- This works no matter how the exceptions interleaves during the execution, because a program can only terminate once.
  -- Generally, in Grisette, to specify the correctness conditions, the user only need to write the program
  -- with exception handling enabled, and specify
  --
  --   1. whether the program can terminate with each exception, and
  --   2. a predicate for the execution result if the program terminate without any exception.
  --
  -- We believe that this is an appropriate and flexible abstraction for program correctness.

  -- ** Monadic symbolic handling in Grisette 
  -- | As shown before, it's no surprise that exception handling can be easily supported in Grisette with 'ExceptT' transformer.
  -- @ExceptT error UnionM value@ represents a multi-path computation that each path can terminate with exceptions of the type @error@,
  -- or terminate with some value of the type @value@ returned. 
  -- 
  -- The following code defines an error type that can be used in Grisette.
  --
  -- >>> :{
  --   data Error = Assert | Assume
  --     deriving (Show, Eq, Generic)
  --     deriving (Mergeable SymBool) via Default Error
  -- :}
  --
  -- A normal execution with a symbolic boolean returned:
  --
  -- >>> mrgReturn "a" :: ExceptT Error UnionM SymBool
  -- ExceptT (UMrg (Single (Right a)))
  --
  -- An abnormal execution terminates with some error:
  --
  -- >>> mrgThrowError Assert :: ExceptT Error UnionM ()
  -- ExceptT (UMrg (Single (Left Assert)))
  --
  -- Then we can define the assert and assume functions,
  -- the function would terminate the execution when the condition is false.
  --
  -- >>> assert cond = mrgIf cond (return ()) (throwError Assert)
  -- >>> assume cond = mrgIf cond (return ()) (throwError Assume)
  -- >>> assert "a" :: ExceptT Error UnionM ()
  -- ExceptT (UMrg (If (! a) (Single (Left Assert)) (Single (Right ()))))
  --
  -- Then a function with verification builtin can be implemented as follows:
  --
  -- > f :: Arg -> Except Error UnionM Res
  -- > f arg = do
  -- >   assume $ precondition arg
  -- >   ...
  -- >   res <- ...
  -- >   assert $ postcondition res
  -- >   mrgReturn res
  --
  -- You can always define your own errors in a similar way.
  -- Grisette also has some error types built in, please check them out at "Grisette.Core#errors".

  -- ** Solver queries
  -- | After symbolic compilation, the result can be sent to the solver for reasoning.
  --
  -- The simplest case is to solve a single symbolic boolean formula.
  -- This can be done by 'solveWith' call, which solves a formula with some configuration.
  -- In the following example, the configuration is @UnboundedReasoning z3@.
  -- We will explain what does it mean later.
  --
  -- >>> solveFormula (UnboundedReasoning z3) (("a" + 1 :: SymInteger) ==~ 4)
  -- Right (Model (fromList [(a :: Integer,3 :: Integer)]))
  --
  -- Grisette also supports a more high level way to express program correctness condition.
  -- The symbolic compilation result with exception handling enabled usually has the type
  -- @ExceptT error UnionM value@, which can be easily converted to a correctness condition
  -- with the 'SolverTranslation' type class, which is defined as follows:
  --
  -- > class SolverTranslation method e v | method -> e v where
  -- >   errorTranslation :: method -> e -> Bool
  -- >   valueTranslation :: method -> v -> Sym Bool
  --
  -- The 'errorTranslation' function decides how to translate the errors.
  -- Given a translation method, it is a /concrete/ predicate on the error types.
  -- If the program is allowed to terminate with some error, then the predicate should return true.
  -- The 'valueTranslation' function is the correctness condition for the program executions without failures.
  -- Given a translation method, it is a /symbolic/ predicate on the error types,
  -- which should be evaluated to true if the program is correct under some model.
  -- 
  -- The translation method could be viewed as a specification for the expected program behavior.
  -- For the scenario of verification of pre-conditions and post-conditions discussed before,
  -- the specification would be the program cannot terminate with assertion violation.
  -- Grisette has builtin support for assert / assume violation errors with 'VerificationConditions',
  -- 'symAssume' and 'symAssert', so we will not use our own error types.
  --
  -- The correctness condition can be defined as follows:
  --
  -- >>> data ViolatesAssertions = ViolatesAssertions
  -- >>> :{
  --   instance SolverErrorTranslation ViolatesAssertions VerificationConditions where
  --     errorTranslation _ AssumptionViolation = False
  --     errorTranslation _ AssertionViolation = True
  --   instance SolverTranslation ViolatesAssertions (Sym Bool) VerificationConditions () where
  --     valueTranslation _ _ = conc False
  -- :}
  --
  -- And we can write the sample program as follows. The @program1@ is a correct program, in which no assertion violation
  -- exception can be thrown. The @program2@ is incorrect, and will throw assertion violation exception when @a@ is 2.
  --
  -- >>> :{
  --   program1 = do
  --     symAssume $ ("a" :: SymInteger) >~ 2
  --     symAssert $ ("a" :: SymInteger) >=~ 2
  --   program2 = do
  --     symAssume $ ("a" :: SymInteger) >=~ 2
  --     symAssert $ ("a" :: SymInteger) >~ 2
  -- :}
  --
  -- We can verify our claim with the solvers:
  --
  -- >>> solveWithExcept ViolatesAssertions (UnboundedReasoning z3) program1
  -- Left Unsat
  -- >>> solveWithExcept ViolatesAssertions (UnboundedReasoning z3) program2
  -- Right (Model (fromList [(a :: Integer,2 :: Integer)]))
  --
  -- Grisette has more flexible ways for expressing solver queries,
  -- we will discuss them later in the [Revisit solver queries](#queries) section.

  -- ** CEGIS loop
  -- | A program synthesis problem can usually be formulated as
  -- \(\exists P. \forall I. \mathrm{assumptions}(P, I)\implies \mathrm{assertions}(P, I)\).
  -- The formula states that we are going to find a program \(P\), such that for any input \(I\) meeting the assumptions,
  -- executing the \(P\) on \(I\) will yield a result meeting the assertions.
  -- Although some solvers support reasoning about interleaved quantifiers,
  -- they are not widely used in synthesis community because they tend not to be very efficient in synthesis problems.
  -- CEGIS is an algorithm to tackle the problem of interleaving quantifiers in program synthesis tasks by
  -- reducing the program synthesis query, i.e. \(\exists\forall\) query to a sequence of
  -- solver calls with quantifier free formulas.
  --
  -- Grisette has support for Counter-example guided inductive synthesis (CEGIS) loops.
  -- Grisette can solve formulas with the form:
  -- \(\exists P. (\exists I. \mathrm{assumptions}(P, I)) \wedge (\forall I. \mathrm{assumptions}(P, I)\implies \mathrm{assertions}(P, I))\)
  -- The left hand side of the conjunction states that we only want non-trivial programs that has at least one valid input.

  -- * Supportive type classes

  -- ** Symbolic equality and ordering

  -- ** Conversion between symbolic and concrete types

  -- ** Merge strategy
  -- | #merge#

  -- ** Generating symbolic values
  -- | #gensym#

  -- *** Revisit solver queries
  -- | #queries#

  -- ** Symbolic hole extraction and evaluation
  

)where

import GHC.Generics
import Grisette
import Data.SBV hiding (Mergeable)
import Control.Monad.State.Lazy
import Control.Monad.Except

-- $setup
-- >>> :set -XDeriveGeneric
-- >>> :set -XDerivingVia
-- >>> :set -XDerivingStrategies
-- >>> :set -XFlexibleContexts
-- >>> :set -XFlexibleInstances
-- >>> :set -XOverloadedStrings
-- >>> :set -XMultiParamTypeClasses
-- >>> import GHC.Generics
-- >>> import Grisette
-- >>> import Data.SBV hiding (Mergeable)
-- >>> import Control.Monad.State.Lazy
-- >>> import Control.Monad.Except
