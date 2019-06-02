#!/bin/bash

if [ "$1" == "-h" ] || [ "$1" == "--help" ]; then
  echo "Usage: ./Base/tool/compile.sh [args]"
  echo
  echo "This script compiles all '.v' files of the Base Coq library."
  echo "If files have been added or removed from the Base library, you should"
  echo "run the 'recompile.sh' script instead."
  echo
  echo "The arguments are forwarded to 'make'. By default all '.v' files are"
  echo "compiled. To compile only specific files, you can specify the"
  echo "corresponding'.vo' files"
  exit 0
fi

if ! [ -f "_CoqProject" ]; then
  echo "This script must be executed from the 'example' directory, i.e."
  echo
  echo "    $> ./Base/tool/compile.sh"
  echo
  echo "Type '$0 --help' for more information."
  exit 1
fi

# Generate make file if it does not exist.
if ! [ -f Makefile ]; then
  coq_files=$(find Base -name "*.v")
  coq_makefile -f _CoqProject $coq_files -o Makefile
fi

# Compile everything by default.
if [ "$#" == "0" ]; then
  make all
else
  make "$@"
fi
