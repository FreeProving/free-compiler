#!/bin/bash

# Print help message.
if [ "$1" == "-h" ] || [ "$1" == "--help" ]; then
  script_dir=$(dirname "$0")
  echo "Usage: ./Base/tool/recompile.sh [args]"
  echo
  echo "This script compiles all '.v' files of the Base Coq library."
  echo "All previously generated files will be removed and a new Makefile"
  echo "is created."
  echo
  echo "The arguments are forwarded to the 'compile.sh' script."
  echo "Type '$script_dir/compile.sh --help' for more information."
  exit 0
fi

# Check working directory
if ! [ -f "_CoqProject" ]; then
  echo "This script must be executed from the 'example' directory, i.e."
  echo
  echo "    \$> ./Base/tool/recompile.sh"
  echo
  echo "Type '$0 --help' for more information."
  exit 1
fi

# Remove generated files.
if [ -f Makefile ]; then
  make clean
  rm Makefile
fi

./Base/tool/compile.sh "$@"
