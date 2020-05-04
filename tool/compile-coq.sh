#!/bin/bash

# Get the name of this script.
script="$0"

# Detect `--recompile` argument.
recompile="false"
if [ "$1" == "--recompile" ]; then
  recompile="true"
  shift
fi

# Print help message.
if [ "$#" = "0" ] || [ "$1" == "-h" ] || [ "$1" == "--help" ]; then
  echo "Usage: $script [--recompile] <coq-dir> [args]"
  echo
  echo "This script compiles all '.v' files in the given directory."
  echo "If files have been added or removed from the directory since the last"
  echo "run, you should add the '--recompile' option."
  echo
  echo "The trailing arguments are forwarded to 'make'. By default all '.v'"
  echo "files are compiled. To compile only specific files, you can specify"
  echo "the corresponding '.vo' files"
  exit 0
fi

# Change into specified directory.
coq_dir="$1"
cd "$coq_dir"
shift

# Optionally remove generated files (if --recompile flag is set).
if [ -f Makefile ] && [ "$recompile" = "true" ]; then
  make clean
  rm Makefile
fi

# Generate make file if it does not exist.
if ! [ -f Makefile ]; then
  # Detect missing `_CoqProject` file.
  if ! [ -f _CoqProject ]; then
    echo "ERROR: Missing '_CoqProject' file" >&2
    exit 1
  fi
  coq_files=$(find . -name "*.v")
  coq_project=$(cat _CoqProject)
  coq_makefile $coq_project $coq_files -o Makefile
fi

# Compile everything by default.
if [ "$#" == "0" ]; then
  make all
else
  make "$@"
fi
