#!/bin/bash

# Change into the compiler's root directory.
script=$(realpath "$0")
script_dir=$(dirname "$script")
root_dir=$(dirname "$script_dir")
cd "$root_dir"

# Call getopt to validate the provided input. 
options=$(getopt -o r --long recompile -- "$@")
[ $? -eq 0 ] || { 
    echo "Incorrect options provided"
    exit 1
}
eval set -- "$options"
while true; do
    case "$1" in
    -r)
        ;& # Fallthrough
    --recompile)
        recompile=true
        ;;
    --)
        shift
        break
        ;;
    esac
    shift
done

# Change into the directory containing the Agda modules.
ARG1=${@:$OPTIND:1}
cd "$ARG1"
echo "Building Agda files in $(pwd)"

# Delete `_build` folder iff the user wants to rebuild everything
if [ "$recompile" = true ] ; then
    echo "Removing _build directory"
    rm -r _build
fi

# check all agda files
for f in $(find . -name "*.agda"); do
  agda "$f"
done
