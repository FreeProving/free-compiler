# Haskell-To-Coq

## Phase 1) Preliminaries

* work through Coq introduction (see [4], 1-12 are well-suited, a demanded-driven approach is probably the best way to learn Coq's syntax and quirks)
* play around with and study current implementation of Haskell-to-Coq-Compiler [1] (e.g. language-coq AST, current transformation approach)
* ask guys and gals from hs-to-coq [2] to publish language-coq as seperate Haskell package for more comfortable reuse

## Phase 2) Generic transformation

* read work about generic transformation of effectful code to Coq (see [3])
* try out/step trough code accompanying the publication
* apply transformation by hand with several examples from Haskell's Data.List/Data.Set module

## Phase 3) Implementation and Testing

* implement transformation from Haskell to Coq using the generic approach
* try out examples done by hand before

## Phase 4) Writing (or skip 'til the end)

## Phase 5) Reevaluation

* evaluate if generated code works "well" (wrt: implicit Arugments, type variables and contexts)
* go to 3) again : )

## Phase 6) Writing

## Optional Features

* generation of induction principles
* transformation of type classes
* transformation of newtypes

[1] https://github.com/beje8442/haskellToCoqCompiler  
[2] https://github.com/antalsz/hs-to-coq  
[3] https://arxiv.org/pdf/1805.08059.pdf  
[4] https://softwarefoundations.cis.upenn.edu/lf-current/toc.html  