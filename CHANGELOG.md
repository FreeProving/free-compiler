# Changelog

## Unrealeased

 - **Added support for sharing**
    + The evaluation strategy can be selected at runtime.
    + There is support for call-by-name, call-by-need and call-by-value evaluation.
 - **Added support for additional effects**
    + Added `trace`ing effect from `Debug.Trace`.
    + Added non-determinism.
      * To use non-determinism in Haskell, you have to add `import FreeC.NonDet` to the top of the module.
      * The module provides the `(?) :: a -> a -> a` and `failed :: a` operators as known from [Curry][curry-lang].
 - **Added Agda back end**
    + The Agda back end does not support sharing or changing of the evaluation strategy in general.
      The evaluation strategy is always call-by-name.
    + Mutually recursive function and data type declarations are not supported.
      The Adga back end uses a different approach to the translation of recursive function declarations using sized types.
      It's not clear whether Agda will always be able to recognize that a function is terminating when our termination checker does.
    + Our Agda base library does not include support for QuickCheck properties at the moment.
      Properties have to be stated manually.
    + The Agda back end does not support the new tracing and non-determinism effects.
       There is only support for partiality.
 - **Added command line options for front- and back end selection**
    + A front end can be specified with `--from LANG`.
    + A back end end can be specified with `--to LANG`.
    + Added IR front end and back end such that the compilers intermediate representation can be used as input / output for debugging purposes.

## [0.2.0.0][tag/v0.2.0.0] / 2020-05-25

 - **Implemented module imports**
    + Imports of the form `import M` are now supported.
    + Module interface files are automatically created for converted modules.
 - **Implemented type inference**
    + Function type signatures are no longer required if the type of the function can be inferred.
    + Type arguments are passed explicitly in the generated Coq code.
 - **Added experimental support for pattern matching compilation**
    + Can be enabled using the `--transform-pattern-matching` command line option.
    + See [`doc/ExperimentalFeatures/PatternMatchingCompilation.md`][] for details and current limitations.
 - **Added decreasing argument pragma**
    + Can be used to bypass our termination checker.
    + See [`doc/CustomPragma/DecreasingArgumentPragma.md`][] for details
 - **Skip some unsupported Haskell features**
    + When the following unsupported Haskell language constructs are encountered, a warning rather than a fatal error is reported.
      * Unrecognized or unsupported pragmas
      * Import specifications (e.g. `import M hiding (...)`)
      * Type class contexts
      * Deriving clauses

## [0.1.0.0][tag/v0.1.0.0] / 2019-09-26

 - **Initial version**

[curry-lang]:
  http://curry-lang.org/
  "Curry Programming Language"

[`doc/ExperimentalFeatures/PatternMatchingCompilation.md`]:
  https://github.com/FreeProving/free-compiler/blob/main/doc/ExperimentalFeatures/PatternMatchingCompilation.md
  "Free Compiler Documentation — Pattern Matching Compilation"
[`doc/CustomPragma/DecreasingArgumentPragma.md`]:
  https://github.com/FreeProving/free-compiler/blob/main/doc/CustomPragma/DecreasingArgumentPragma.md
  "Free Compiler Documentation — Decreasing Argument Pragma"

[tag/v0.1.0.0]:
  https://github.com/FreeProving/free-compiler/tree/v0.1.0.0
  "Free Compiler v0.1.0.0"
[tag/v0.2.0.0]:
  https://github.com/FreeProving/free-compiler/tree/v0.2.0.0
  "Free Compiler v0.2.0.0"
