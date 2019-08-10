#!/bin/bash

# Change into the root directory of the Base library.
script=$(realpath "$0")
script_dir=$(dirname "$script")
base_lib_dir=$(dirname "$script_dir")
cd "$base_lib_dir"

# Print help message.
if [ "$1" == "-h" ] || [ "$1" == "--help" ]; then
  echo "Usage: $script [args]"
  echo
  echo "This script compiles all '.v' files of the Base Coq library."
  echo "If files have been added or removed from the Base library, you should"
  echo "run the 'recompile.sh' script instead."
  echo
  echo "The arguments are forwarded to 'make'. By default all '.v' files are"
  echo "compiled. To compile only specific files, you can specify the"
  echo "corresponding '.vo' files"
  exit 0
fi

# Generate make file if it does not exist.
if ! [ -f Makefile ]; then
  coq_files=$(find . -name "*.v")
  coq_makefile -f _CoqProject $coq_files -o Makefile
fi

# Compile everything by default.
if [ "$#" == "0" ]; then
  make all
else
  make "$@"
fi
