#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

for f in $(find . -name "*.agda")
  do agda "$f"
done