#!/bin/bash

# Pass all arguments to the compiler.
cabal new-run haskell-to-coq-compiler -- "$@"
