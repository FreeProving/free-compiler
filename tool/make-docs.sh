#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath $0)
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Colored output.
red=$(tput setaf 1)
bold=$(tput bold)
reset=$(tput sgr0)

# Helper function to print error messages.
function printErrorAndDie() {
  echo "${bold}"
  echo "----------------------------------------------------------------------"
  echo "${reset}"
  echo "${red}${bold}Error:${reset}" \
       "${bold}$1${reset}"
  exit 1
}

# Make temporary file for Haddock output.
haddock_output=$(mktemp)

# Run tests with cabal.
cabal new-haddock --haddock-all                   \
                  --haddock-hyperlink-source 2>&1 | tee "$haddock_output"

# Cabal currently does not set the exit status correctly when the Haddock
# command fails. Thus we have to set the exit status ourselves.
if grep "Warning: Failed to build documentation for" "$haddock_output"; then
  printErrorAndDie "Failed to build documentation"
fi

# Since there are many warnings that Haddock cannot find link destinations
# for identifiers from external packages, print a more noticable error message
# at the end if the documentation comments actually contain a reference to
# an identifier that is not in scope.
if grep -P "Warning: '\w*' is out of scope" "$haddock_output"; then
  printErrorAndDie "The documentation contains out of scope identifiers"
fi
