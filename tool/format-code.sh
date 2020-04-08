#!/bin/bash

# This script can be used to format Haskell source code files using `brittany`
# automatically. Note that this script overwrites source files. Make sure
# to backup your files beforehand (e.g. by `git add`ing them).

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
if ! which brittany; then
  echo "${red}${bold}Error:${reset}" \
       "${bold}Could not find Brittany.${reset}"
  echo " |"
  echo " | Run the ${bold}cabal new-install brittany${reset} to install it."
  echo " | Also make sure that ${bold}brittany${reset} is in your" \
       "${bold}\$PATH${reset}!"
  exit 1
fi

# Format all Haskell files using Brittany.
for file in $(find src -name '*.hs' -type f); do
  echo -n "Formatting ${bold}$file${reset} ... "
  hash_before=$(sha256sum "$file")
  brittany --write-mode=inplace "$file"
  if [ "$?" == "0" ]; then
    hash_after=$(sha256sum "$file")
    if [ "$hash_before" == "$hash_after" ]; then
      echo "${bold}UNCHANGED${reset}"
    else
      echo "${green}${bold}DONE${reset}"
    fi
  else
    echo "${red}${bold}ERROR${reset}"
  fi
done
