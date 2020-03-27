#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath $0)
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Make temporary file for Haddock output.
haddock_output=$(mktemp)

# Run tests with cabal.
cabal new-haddock --haddock-hyperlink-source 2>&1 | tee "$haddock_output"

# Cabal currently does not set the exit status correctly when the Haddock
# command fails. Thus we have to set the exit status ourselves.
if grep "Warning: Failed to build documentation for" "$haddock_output"; then
  exit 1
fi
