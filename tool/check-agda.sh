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
  echo "Usage: $script [options...] <agda-dir> -- [args]"
  echo
  echo "This script compiles all '.agda' files in the given directory."
  echo "The trailing arguments are forwarded to the Agda compiler."
  echo
  echo "Command line options:"
  echo "  -h    --help         Display this message."
  echo "  -r    --recompile    Force recompilation of all Agda files"
  echo "                       by removing the '_build' directory first."
  exit 0
fi

# Change into the directory containing the Agda modules.
agda_dir=$1
cd "$agda_dir"
shift
echo "Compiling Agda files in $agda_dir ..."

# Delete `_build` directory if the `--recompile` flag is set.
if [ -f _build ] && [ "$recompile" = true ]; then
  echo "Removing _build directory ..."
  rm -r _build
fi

# Check all `.agda` files. All remaining command line options are forwarded
# to the Agda compiler.
for f in $(find . -name "*.agda"); do
  agda "$f" "$@"
done
