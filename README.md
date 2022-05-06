# Grisette

[![CircleCI](https://circleci.com/gh/lsrcz/grisette-haskell/tree/main.svg?style=svg&circle-token=feae0d11f5760b7966cc8f694337f26317c26b1a)](https://circleci.com/gh/lsrcz/grisette-haskell/tree/main) [![Coverage Status](https://coveralls.io/repos/github/lsrcz/grisette-haskell/badge.svg?branch=main&t=ec2wZa&kill_cache=1)](https://coveralls.io/github/lsrcz/grisette-haskell?branch=main&t=ec2wZa&kill_cache=1)

## Components in this repo

- [`grisette-core`](grisette-core) folder contains the core constructs for Grisette, includes most of the things shown in the paper.
  The actual implementation is more flexible than the one described in the paper.
  It allows the user to defined his own symbolic intermediate representations (the `SymBool`, `SymInteger` types in the paper),
  when using another representation (e.g. BDDs) could be beneficial.
- [`grisette-symir`](grisette-symir) folder contains our implementation for `SymBool` and `SymInteger`.
- [`grisette-backend-sbv`](grisette-backend-sbv) folder contains our backend that lowers from the symbolic IR to SMT formula using sbv package.
- [`grisette-backend-direct`](grisette-backend-direct) (WIP, does not work now) We are working on an alternative backend for performance.
- [`grisette-lib`](grisette-lib) folder contains some lifted library functions, e.g. symbolic filter, etc.
  There aren't many functions there as usually the user can define their own version easily.
- [`grisette`](grisette) folder provides `Grisette` module, and the user can import everything from `grisette-core`, `grisette-symir`, `grisette-backend-sbv` and `grisette-lib` by importing it.
- [`grisette-examples`](grisette-examples) folder contains some example use cases of Grisette. Many of them are moved to the `grisette-benchmarks` folder.
- [`grisette-benchmarks`](grisette-benchmarks) folder contains the benchmarks used in ICFP'22 submission.
- [`grisette-scratch`](grisette-scratch) folder contains experimental code.
- [`grisette-tutorial`](grisette-tutorial) (WIP, not ready for read now) contains tutorials in Haddock format
- [`grisette-doctest`](grisette-doctest) package contains a single doctest test that checks everything in the Haddock documentation.
- [`scripts`](scripts) are some scripts for running the benchmarks.

## Documentation
Documentation for `grisette-core` is (partly) available. Most of them should be up to date.
You can build them with Haddock, or direct view them in the source files.

## Directories and source files that may be most interesting
- [`grisette-examples/assert-assume-icfp2022`](grisette-examples/assert-assume-icfp2022) clarifies what `assert` and `assume` means in Rosette (and our paper).
- [`grisette-examples/expr-icfp2022`](grisette-examples/expr-icfp2022) is the fixed and updated version for the code in Section 3.1.
   Details are explained.
- [`grisette-scratch/effects`](grisette-scratch/effects) shows how Grisette works with `fused-effects` effect handler library.
- [`grisette-benchmarks/regex*`](grisette-benchmarks/regex). The regex synthesizer written with Coroutine shown in Section 3.2.

## Other directories and source files that may be interesting
- [`grisette-core/src/Grisette/Data/UnionBase.hs`](grisette-core/src/Grisette/Data/UnionBase.hs) for Reviewer D:
  > l677: I'd quite like to see these rules - at least in an appendix if not in the body of the paper. You should be careful about using the word "trivial". These rules may be unsurprising, but I doubt they're actually completely trivial.
- [`grisette-core/src/Grisette/Data/Class`](grisette-core/src/Grisette/Data/Class/) contains the various type classes for everything you need
  to build a symbolic evaluator.

## The benchmarks
- [`grisette-benchmarks/bonsai*`](grisette-benchmarks/bonsai-lib/). Bonsai is a data structure specialized for efficient type system verification with symbolic evaluation.
The type system verification methodology in that paper is similar to the one described in the example in section 3.1,
but with the AST trees replaced with a novel Bonsai tree, which is more efficient in all-path symbolic execution with merging scenario.
The adoption of Bonsai trees allows more efficient reasoning for type systems, and allows to find the bugs in real world type systems,
e.g. NanoScala (DOT type system, which is known to be unsound when null references are included) and LetPoly (let-polymorphism with mutable references and higher-order functions, which represents a historical bug in ML).
- [`grisette-benchmarks/cosette*`](grisette-benchmarks/cosette/). Cosette is an automated prover for SQL.
It executes SQL queries symbolically, and is designed to decide SQL query equivalence.
- [`grisette-benchmarks/ferrite`](grisette-benchmarks/ferrite/). Ferrite is a tool for specifying and checking file system crash-consistency models. The file system crash-consistency model describes the allowed and forbidden behaviors of a file system across crashes. Ferrite is capable of verifying that a file system implementation meets the specification, or synthesizing sufficient barriers to ensure that the program with file I/O system calls satisfies the desired crash-safety properties.
- [`grisette-benchmarks/fluidics`](grisette-benchmarks/fluidics/). Fluidics is a small DSL for synthesizing microfluidics array manipulation.
- [`grisette-benchmarks/ifcl`](grisette-benchmarks/ifcl/). IFCL is a functional symbolic DSL for specifying and verifying executable semantics of abstract stack-and-pointer machines that track dynamic information flow to enforce security properties.

## Changed API
The artifact version is newer than the paper version, and some APIs are changed.
We will update the code in the paper to be consistent with the current status of the code.
