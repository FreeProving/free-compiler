#!/bin/bash

# This script can be used to run the compiler for debugging purposes. It
# compiles and executes the compiler using Cabal. The command line options
# are forwarded to the compiler.
#
# During debugging the `-Wwarn` flag of GHC is set such that warnings are not
# fatal. However, the compiler is intended to compile without warnings, during
# production. Thus, the `-Wall` and `-Werror` flags are set by default.
# Before local changes are pushed, all warnings should be fixed. Otherwise,
# the CI pipeline will fail.

# Change into the compiler's root directory.
script=$(realpath $0)
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Disable fatal warnings and forward arguments to compiler.
cabal new-run haskell-to-coq-compiler --ghc-option -Wwarn -- "$@"
