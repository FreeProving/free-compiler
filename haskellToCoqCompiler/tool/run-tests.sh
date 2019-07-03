#!/bin/bash

# Change into the compiler's root directory.
script="$0"
script_dir=$(dirname "$script")
cd "$script_dir"

# Run tests with cabal.
cabal test all --test-show-details=direct --test-option=--format=progress
