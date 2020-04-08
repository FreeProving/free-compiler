#!/bin/bash

# This script can be used to check whether there are Haskell source files that
# have not been formatted using `brittany`. It is used by the CI pipeline and
# the `./tool/full-test.sh` script.
# Use `./tool/format-code.sh` to format all source files automatically.

# Change into the compiler's root directory.
script=$(realpath $0)
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Colored output.
red=$(tput setaf 1)
green=$(tput setaf 2)
bold=$(tput bold)
reset=$(tput sgr0)

# Check whether brittany is installed.
if ! which brittany >/dev/null 2>&1; then
  echo "${red}${bold}Error:${reset}" \
       "${bold}Could not find Brittany.${reset}"
  echo " |"
  echo " | Run the ${bold}cabal new-install brittany${reset} to install it."
  echo " | Also make sure that ${bold}brittany${reset} is in your" \
       "${bold}\$PATH${reset}!"
  exit 1
fi

# The user can optionally specify files and directories to check.
# By default all Haskell files in the `src` and `example` directories are
# checked.
files=("$@")
if [ "${#files[@]}" == "0" ]; then
  files=(src example)
fi

# Format all given Haskell files that are tracked by `git` using `brittany`
# and compare the output with the original file. Count the number of files
# that need formatting.
counter=0
for file in $(find "${files[@]}" -name '*.hs' -type f); do
  if git ls-files --error-unmatch "$file" >/dev/null 2>&1; then
    echo -n "Checking ${bold}$file${reset} ... "
    if brittany "$file" | cmp -s "$file"; then
      echo "${green}${bold}OK${reset}"
    else
      echo "${red}${bold}NEEDS FORMATTING${reset}"
      counter=$(expr $counter + 1)
    fi
  fi
done

# Test whether there are any files that need formatting.
if [ "$counter" -gt "0" ]; then
  echo "${bold}"
  echo "----------------------------------------------------------------------"
  echo "${reset}"
  echo "${red}${bold}Error:${reset}" \
       "${bold}Some Haskell files need formatting.${reset}"
  echo " |"
  echo " | Run the ${bold}./tool/format-code.sh${reset} script to format all"
  echo " | files automatically."
  exit 1
fi
