#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# change into the agda base-lib dir (location of `.agda-lib` file)
cd base/agda

# check options
while getopts "r" opt; do
  case $opt in
    r)
      rm -r _build
      ;;
    \?)
      exit 1
      ;;
  esac
done

# check all agda files
for f in $(find . -name "*.agda")
  do agda "$f"
done