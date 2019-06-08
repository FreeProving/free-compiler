#!/bin/bash

script="$0"
script_dir=$(dirname "$script")

# Find directory of input file.
input_file="$1"
if [ "$input_file" == "--watch" ]; then
  input_file="$2"
fi
if [ -z "$input_file" ]; then
  echo "Usage: $0 [--watch] path/to/input-file.md [args]"
  exit 0
fi
input_dir=$(dirname "$input_file")

# Install bower dependencies.
if ! [ -d "$input_dir/bower_components" ]; then
  owd=$(pwd)
  cd "$input_dir"

  # Create bower project if it does not exist.
  if ! [ -f "bower.json" ]; then
    bower init
    bower install --save reveal.js
  else
    bower install
  fi

  # Return to original working directory.
  cd "$owd"
fi

# Forward all arguments and add beamer arguments.
export output_type="revealjs"
"$script_dir"/typeset.sh "$@"                \
  -V revealjs-url=bower_components/reveal.js \
  --slide-level=2
