#!/bin/bash

# Change into directory containing the Base directory.
script="$0"
script_dir=$(dirname "$script")
cd "$script_dir/../.."

# Print help message.
if [ "$1" == "-h" ] || [ "$1" == "--help" ]; then
  echo "Usage: $script [args]"
  echo
  echo "This script compiles all '.v' files of the Base Coq library."
  echo "All previously generated files will be removed and a new Makefile"
  echo "is created."
  echo
  echo "The arguments are forwarded to the 'compile.sh' script."
  echo "Type '$script_dir/compile.sh --help' for more information."
  exit 0
fi

# Remove generated files.
if [ -f Makefile ]; then
  make clean
  rm Makefile
fi

./Base/tool/compile.sh "$@"
