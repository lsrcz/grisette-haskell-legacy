# Supplementary Material for POPL 2023 Submission: 



## The repo organization
This repository contains Grisette, a monadic library for symbolic evaluator construction
which is under development.

### `grisette-core` 
The [](grisette-core) package contains the core constructs for Grisette.
The implementation of the Union data structure is at
[UnionBase.hs](grisette-core/src/Grisette/Core/Data/UnionBase.hs).
This data structure is more general than the version discussed in the paper,
with the symbolic boolean type configurable.


[UnionMBase.hs](grisette-core/src/Grisette/Core/Control/Monad/UnionMBase.hs) contains the `UnionM` (actually more general `UnionMBase`) monad from the paper.

The various type classes supporting symbolic compilation is implemented at [](grisette-core/src/Grisette/Core/Data/Class).
- [BitVector.hs](grisette-core/src/Grisette/Core/Data/Class/BitVector.hs), [Bool.hs](grisette-core/src/Grisette/Core/Data/Class/Bool.hs), [Integer.hs](grisette-core/src/Grisette/Core/Data/Class/Integer.hs). [Function.hs](grisette-core/src/Grisette/Core/Data/Class/Function.hs) are aggregated constraints for the various symbolic primitives.
- [Error.hs](grisette-core/src/Grisette/Core/Data/Class/Error.hs) contains helpers for error handling.
- [Evaluate.hs](grisette-core/src/Grisette/Core/Data/Class/Evaluate.hs) is for evaluation given satisfiable solutions.
- [Mergeable.hs](grisette-core/src/Grisette/Core/Data/Class/Mergeable.hs) and [SimpleMergeable.hs](grisette-core/src/Grisette/Core/Data/Class/SimpleMergeable.hs) are for merging.
- [SOrd.hs](grisette-core/src/Grisette/Core/Data/Class/SOrd.hs) is for symbolic `Ord` type class. Symbolic `Eq` class is defined at [Bool.hs](grisette-core/src/Grisette/Core/Data/Class/Bool.hs)
- [ToCon.hs](grisette-core/src/Grisette/Core/Data/Class/ToCon.hs) and [ToSym.hs](grisette-core/src/Grisette/Core/Data/Class/ToSym.hs) provides the conversion between concrete and symbolic types.
- [Solver.hs](grisette-core/src/Grisette/Core/Data/Class/Solver.hs) contains the solver interfaces.

### `grisette-symir`
We provide a symbolic primitive type implementation at the [grisette-symir](grisette-symir) package, which is based on SMTLIB2 language.
The user may design their own symbolic primitives with other techniques, e.g., BDDs, if appropriate for their tasks.

### `grisette-backend-sbv`
This package contains our backend solver interface implemented using `sbv`.

### `grisette-backend-direct`
In the future, this would be a package for an alternative backend directly talk to the solvers without external packages. Not available now.

### `grisette-fused-effects`, `grisette-monad-coroutine`, `grisette-vector-sized`
Supporting some external libraries.
The support for bitvectors is built into `grisette-core`.

### `grisette-benchmarks`
Implementation of the benchmark programs.

### `grisette-unordered`
Implementation of the benchmark programs with MEG semantics.

### `grisette-cbmcencoding`
Implementation of the benchmark programs with CBMC error encoding.

### `grisette`
Aggregated package for `grisette-core`, `grisette-symir`, `grisette-lib` and `grisette-sbv`.

### Other `grisette-*` folders
Other folders contains the files used during our development, may be obsolete.

### `scripts`
Contains the scripts used for our evaluation.
The `report.py` won't work without results for Rosette benchmarks, which is not anonymized at this time and packed in this repo.

The `runallbench.sh` can be used to execute all the benchmarks.
`./scripts/runallbench.sh -n 5 all` runs all the benchmarks with ORG semantics (including CBMC error encoding benchmarks) for 5 times and take the average metrics.
`./scripts/runallbench.sh -u -n 5 all` runs all
benchmarks with MEG semantics.

## The benchmarks
- [`grisette-benchmarks/bonsai*`](grisette-benchmarks/bonsai-lib/). Bonsai is a data structure specialized for efficient type system verification with symbolic evaluation.
The type system verification methodology in that paper is similar to the one described in the example in section 3.1,
but with the AST trees replaced with a novel Bonsai tree, which is more efficient in all-path symbolic execution with merging scenario.
The adoption of Bonsai trees allows more efficient reasoning for type systems, and allows to find the bugs in real world type systems,
e.g. NanoScala (DOT type system, which is known to be unsound when null references are included) and LetPoly (let-polymorphism with mutable references and higher-order functions, which represents a historical bug in ML).
You can execute them with `stack run bonsai-nanoscala` or `stack run bonsai-letpoly`.
- [`grisette-benchmarks/cosette*`](grisette-benchmarks/cosette/). Cosette is an automated prover for SQL.
It executes SQL queries symbolically, and is designed to decide SQL query equivalence.
You can execute it with `stack run cosette` or `stack run cosette-optimized-merge`.
- [`grisette-benchmarks/ferrite`](grisette-benchmarks/ferrite/). Ferrite is a tool for specifying and checking file system crash-consistency models. The file system crash-consistency model describes the allowed and forbidden behaviors of a file system across crashes. Ferrite is capable of verifying that a file system implementation meets the specification, or synthesizing sufficient barriers to ensure that the program with file I/O system calls satisfies the desired crash-safety properties.
You can execute it with `stack run ferrite`.
- [`grisette-benchmarks/fluidics`](grisette-benchmarks/fluidics/). Fluidics is a small DSL for synthesizing microfluidics array manipulation.
You can execute it with `stack run fluidics`.
- [`grisette-benchmarks/ifcl`](grisette-benchmarks/ifcl/). IFCL is a functional symbolic DSL for specifying and verifying executable semantics of abstract stack-and-pointer machines that track dynamic information flow to enforce security properties.
You can execute it with `stack run ifcl`.
- [`grisette-benchmarks/regex*`](grisette-benchmarks/regex-common/)
The backtracking regex benchmarks implemented using delimited continuations and free monad transformers.
You can run the delimited continuation version by `stack run regex-delim`, and the free monad transformer version by `stack run regex`.


The no memoization versions have the suffix `-nomemo`. The CBMC versions have the suffix `-cbmc`. The MEG versions have the suffix `-unordered`.


## Run the Benchmarks

The repo is managed with The project is managed with [Stack](https://docs.haskellstack.org/en/stable/README/).
You can install Grisette with `stack install`.

This is not required, as you can always run the benchmarks with `stack run <benchmark-executable-name>`.
In this case, please make sure that a recent `z3` or `boolector` (depending on the benchmark) is accessible via the `PATH`.


