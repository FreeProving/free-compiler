# Translation from Haskell to Coq

## Outline

### Introduction, Motivation, Objectives

-   What is Haskell?
-   What is Coq?
-   Why translate Haskell to Coq?
-   Which existing approaches exist?
-   What do we want to do differently?

### Free Monad

-   What is the free monad and why do we need the free monad?
-   Problems with the free monad in Coq.

### Assumptions

-   Subset of Haskell that the compiler should be able to translate.
-   Predefined functions and data types.
-   The Haskell program must be typed correctly.

### Translation

1.  Translation of types
2.  Translation of data type declarations
    -   Translation of type constructors
3.  Translation of expressions
4.  Translation of non-recursive functions
    -   Translation of function and constructor applications
5.  Translation of (mutually) recursive functions
6.  Translation of QuickCheck properties

### Correctness of translation

-   Similarities of worker/wrapper transformation with translation of (simple)
    recursive functions.
-   ...

### Implementation

-   Used libraries (`haskell-src-exts`, `language-coq`)
-   Simplified AST for Haskell programs.
-   Translation outline
    -   Parsing
    -   Convert to simplified AST
    -   Dependency analysis
    -   Convert to Coq AST
    -   "Pretty" print
- Base library

### Case-Study

-   Are the assumptions too restrictive for real world examples?
-   Can the generated code be used to proof (simple) properties?

### Limitations & Future work

-   Explicit pattern matching (→ Malte)
-   No type classes (e.g. equality only for integers)
-   Higher-order functions
-   Induction principles
-   Proof correctness

### Conclusion
