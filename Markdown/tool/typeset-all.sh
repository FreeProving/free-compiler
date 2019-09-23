#!/bin/bash

script="$0"
script_dir=$(dirname "$script")

# Parse command line arguments.
typeset_script="typeset"
if [[ "$1" == "--beamer" ]]; then
  typeset_script="typeset-beamer"
  shift
elif [[ "$1" == "--revealjs" ]]; then
  typeset_script="typeset-revealjs"
  shift
fi

# Print help message if there is no input directory.
if [[ "$#" -lt 1 ]]; then
  echo "Usage: $script [--beamer|--revealjs] <INPUT-DIR> [PANDOC-OPTIONS]"
  exit 1
fi

# Get input directory.
input_dir="$1"
shift

# Typeset all Markdown files in the input directory.
input_files=$(find "$input_dir" -type d -name "bower_components" -prune -o -name "*.md" -print)
for input_file in $input_files; do
  "$script_dir/$typeset_script.sh" "$input_file" "$@"
  echo "------------------------------------------"
done
