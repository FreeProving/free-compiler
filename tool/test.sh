#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath $0)
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Run tests with cabal.
# We use `new-run` instead of `new-test`, because Cabal 2.4 does not
# support `--test-options` to be passed to the test.
cabal new-run unit-tests -- "$@"
