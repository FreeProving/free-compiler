#!/bin/bash

# Pass all arguments to the compiler.
cabal run haskell-to-coq-compiler -- "$@"
