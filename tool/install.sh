#!/bin/bash

# This script installs the compiler via the `cabal new-install` command.
# The Cabal command cannot be used directly since we have to perform some
# setup actions even before the sdist tarball is created by Cabal.
#
# All command line options that are passed to this script are forwarded to
# Cabal such that the user can still customize the installation.

# Change into the compiler's root directory.
script=$(realpath $0)
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Write the precise version of the compiler to a file in the root directory.
if which git >/dev/null && [ -d .git ]; then
  git describe --always --dirty > VERSION
else
  echo 'unknown' > VERSION
fi

# Clean up the `VERSION` file when installation is done or canceled, e.g., by
# pressing `CTRL+C`.
function cleanup() {
  if [ -f VERSION ]; then
    rm VERSION
  fi
}
trap cleanup INT TERM EXIT

# Install the compiler from the previously created source distribution archive.
# If the compiler is installed already, it is reinstalled.
cabal new-install --overwrite-policy=always "$@" freec
