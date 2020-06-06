#!/bin/bash

# Get the name of this script.
script="$0"

# Set default values for command line options.
help=false
recompile=false

# Parse command line options.
options=$(getopt -o hr --long help,recompile -- "$@")
if [ $? -ne 0 ]; then
  echo
  echo "Type '$script --help' for more information."
  exit 1
fi
eval set -- "$options"
while true; do
  case "$1" in
  -h | --help) help=true; shift ;;
  -r | --recompile) recompile=true; shift ;;
  --) shift; break ;;
  *) break ;;
  esac
done

# Print usage information if the `--help` flag is set.
if [ "$help" = true ]; then
  echo "Usage: $script [options...] <coq-dir> -- [args]"
  echo
  echo "This script compiles all '.v' files in the given directory."
  echo "If files have been added or removed from the directory since the last"
  echo "run, you should add the '--recompile' option."
  echo
  echo "The trailing arguments are forwarded to 'make'. By default all '.v'"
  echo "files are compiled. To compile only specific files, you can specify"
  echo "the corresponding '.vo' files"
  echo
  echo "Command line options:"
  echo "  -h    --help         Display this message."
  echo "  -r    --recompile    Force recompilation of all Coq files"
  echo "                       by running 'make clean' and regenerate"
  echo "                       the Makefile."
  exit 0
fi

# Change into specified directory.
coq_dir="$1"
if ! [ -d "$coq_dir" ]; then
  echo "Error: Could not find directory $coq_dir"
  exit 1
fi
cd "$coq_dir"
shift
echo "Compiling Coq files in $coq_dir ..."

# Optionally remove generated files (if `--recompile` flag is set).
if [ -f Makefile ] && [ "$recompile" = true ]; then
  echo "Removing build products and Makefile ..."
  make clean
  rm Makefile
fi

# Generate make file if it does not exist.
if ! [ -f Makefile ]; then
  echo "Generating Makefile ..."
  # Detect missing `_CoqProject` file.
  if ! [ -f _CoqProject ]; then
    echo "ERROR: Missing '_CoqProject' file" >&2
    exit 1
  fi
  # The `_CoqProject` file is inlined into the `coq_makefile` command
  # since the `-f` command line option sometimes seems to be ignored
  # for some reason.
  coq_files=$(find . -name "*.v")
  coq_project=$(cat _CoqProject)
  coq_makefile $coq_project $coq_files -o Makefile
fi

# Compile everything by default.
echo "Running 'make' ..."
if [ "$#" == "0" ]; then
  make all
else
  make "$@"
fi
