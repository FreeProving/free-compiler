#!/bin/bash

# This script can be used to check whether there are Haskell source files that
# have not been formatted using `floskell` or contains non-Unix line endings.
# It is used by the CI pipeline and the `./tool/full-test.sh` script.
# Use `./tool/format-code.sh` to format all source files automatically.

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

# Check whether floskell is installed.
if ! which floskell >/dev/null 2>&1; then
  echo "${red}${bold}Error:${reset}" \
       "${bold}Could not find Floskell.${reset}"
  echo " |"
  echo " | Run the ${bold}cabal new-install floskell${reset} to install it."
  echo " | Also make sure that ${bold}floskell${reset} is in your" \
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

# Check all given Haskell files that are tracked by `git` and count the number
# of files that are not formatted or encoded correctly.
error_counter=0
format_counter=0
line_ending_counter=0
for file in $(find "${files[@]}" -name '*.hs' -type f); do
  # Skip files that are not tracked by git.
  if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1 ||
       git ls-files --error-unmatch "$file" >/dev/null 2>&1; then
    echo -n "Checking ${bold}$file${reset} ... "
    is_okay=0

    # Test whether the file uses Windows line endings (CRLF) or mixed line
    # endings instead of Unix line endings (LF) by deleting all carriage
    # return (CR) characters and comparing the output to the original file.
    if ! tr -d '\r' <"$file" | cmp -s "$file"; then
      echo -n "${yellow}${bold}HAS WRONG LINE ENDINGS${reset}"
      line_ending_counter=$(expr $line_ending_counter + 1)
      is_okay=1
    fi

    # Create temporary directory for Floskell errors.
    error_log=$(mktemp)

    # Test whether the file is formatted by formatting it and comparing the
    # output to the original file.
    if ! cat "$file" | floskell 2>"$error_log" | cmp -s "$file"; then
      if [ "$is_okay" -ne "0" ]; then
        echo -n " and "
      fi
      if [ -s "$error_log" ]; then
        echo -n "${red}${bold}ERROR${reset}"
        error_counter=$(expr $format_counter + 1)
      else
        echo -n "${red}${bold}NEEDS FORMATTING${reset}"
        format_counter=$(expr $format_counter + 1)
      fi
      is_okay=1
    fi

    if [ "$is_okay" -eq "0" ]; then
      echo "${green}${bold}OK${reset}"
    else
      echo ""
    fi

    # Print error log and suggestions for how to fix the errors to the console.
    sed 's/^/ \| /' "$error_log"
    if grep -q 'Ambiguous infix expression' "$error_log"; then
      echo " |"
      echo " | Make sure all infix operators are listed in the" \
           "${bold}floskell.json${reset} configuration file!"
    fi

    # Clean up.
    rm "$error_log"
  else
    echo "Skipping ${bold}$file${reset} ... ${bold}NOT TRACKED${reset}"
  fi
done

# By default, the script returns `0`. If any check below failed, the
# exit code is set to `1`.
exit_code=0

# Test whether there are any files that are not encoded properly.
if [ "$line_ending_counter" -gt "0" ]; then
  echo "${bold}"
  echo "----------------------------------------------------------------------"
  echo "${reset}"
  echo "${yellow}${bold}Warning:${reset}" \
       "${bold}Some Haskell files don't use Unix line endings.${reset}"
  echo " |"
  echo " | Run the ${bold}./tool/format-code.sh${reset} script to normalize"
  echo " | line endings automatically."
  exit_code=1
fi

# Test whether there are any files that need formatting.
if [ "$format_counter" -gt "0" ]; then
  echo "${bold}"
  echo "----------------------------------------------------------------------"
  echo "${reset}"
  echo "${red}${bold}Error:${reset}" \
       "${bold}Some Haskell files need formatting.${reset}"
  echo " |"
  echo " | Run the ${bold}./tool/format-code.sh${reset} script to format all"
  echo " | files automatically."
  exit_code=1
fi

# Test whether there are any files that need formatting.
if [ "$error_counter" -gt "0" ]; then
  echo "${bold}"
  echo "----------------------------------------------------------------------"
  echo "${reset}"
  echo "${red}${bold}Error:${reset}" \
       "${bold}Floskell failed to process some Haskell files.${reset}"
  echo " |"
  echo " | Fix the errors and run the script again."
  exit_code=1
fi

# If any check above failed, the script exists with error code `1`.
exit "$exit_code"
