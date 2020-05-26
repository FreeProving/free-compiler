#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# consume parameters
while getopts "r" opt; do
  case $opt in
    r)
      rebuild=true
      ;;
    \?)
      exit 1
      ;;
  esac
done

# Change into the directory containing the Agda modules.
ARG1=${@:$OPTIND:1}
cd "$ARG1"
echo "Building Agda files in $(pwd)"

# Delete `_build` folder iff the user wants to rebuild everything
if [ "$rebuild" = true ] ; then
    echo "Removing _build directory"
    rm -r _build
fi

# check all agda files
for f in $(find . -name "*.agda"); do
  agda "$f"
done
