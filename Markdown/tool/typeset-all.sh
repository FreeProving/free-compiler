#!/bin/bash

script="$0"
script_dir=$(dirname "$script")

if [[ "$#" -lt 1 ]]; then
  echo "Usage: $script <INPUT-DIR> [PANDOC-OPTIONS]"
  exit 1
fi

# Get input directory.
input_dir="$1"
shift

# Typeset all Markdown files in the input directory.
input_files=$(find "$input_dir" -name "*.md")
for input_file in $input_files; do
  "$script_dir/typeset.sh" "$input_file" "$@"
  echo "------------------------------------------"
done
