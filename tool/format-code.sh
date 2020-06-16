#!/bin/bash

# This script can be used to format Haskell source code files using `brittany`
# automatically. The line endings of the source file are converted to
# Unix line endings (LF). Note that this script overwrites source files.
# It is strongly recommended to backup your files beforehand (e.g., by
# `git add`ing them).

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Colored output.
red=$(tput setaf 1)
green=$(tput setaf 2)
yellow=$(tput setaf 3)
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

# The user can optionally specify files and directories to format.
# By default all Haskell files in the `src` and `example` directories are
# formatted.
files=("$@")
if [ "${#files[@]}" == "0" ]; then
  files=(src example)
fi

# Format all given Haskell files that are tracked by `git` using `brittany`.
for file in $(find "${files[@]}" -name '*.hs' -type f); do
  if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1 ||
       git ls-files --error-unmatch "$file" >/dev/null 2>&1; then
    echo -n "Formatting ${bold}$file${reset} ... "
    unchanged=0

    # Convert Windows line endings (CRLF) to Unix line endings (LF) by
    # removing all carriage return (CR) bytes.
    temp_file=$(mktemp)
    cp "$file" "$temp_file"
    hash_before=$(sha256sum "$temp_file")
    tr -d '\r' <"$file" >"$temp_file"
    if [ "$?" -eq "0" ]; then
      hash_after=$(sha256sum "$temp_file")
      if [ "$hash_before" != "$hash_after" ]; then
        echo -n "${yellow}${bold}NORMALIZED LINE ENDINGS${reset}"
        unchanged=1
      fi
    else
      echo "${red}${bold}ERROR${reset}"
      continue
    fi

    # Format code with Brittany.
    hash_before=$(sha256sum "$temp_file")
    brittany --write-mode=inplace "$temp_file"
    if [ "$?" -eq "0" ]; then
      hash_after=$(sha256sum "$temp_file")
      if [ "$hash_before" != "$hash_after" ]; then
        if [ "$unchanged" -ne "0" ]; then
          echo -n " and "
        fi
        echo -n "${green}${bold}HAS BEEN FORMATTED${reset}"
        unchanged=1
      fi
    else
      echo "${red}${bold}ERROR${reset}"
      continue
    fi

    # Overwrite file if it has changed and clean up temporary file otherwise.
    if [ "$unchanged" -eq "0" ]; then
      echo "${bold}UNCHANGED${reset}"
      rm "$temp_file"
    else
      echo ""
      mv "$temp_file" "$file"
    fi
  else
    echo "Skipping ${bold}$file${reset} ... ${bold}NOT TRACKED${reset}"
  fi
done
