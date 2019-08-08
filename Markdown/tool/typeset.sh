#!/bin/bash

script="$0"
script_dir=$(dirname "$script")
pandoc_scripts_dir=$(realpath "$script_dir/pandoc-scripts")

# Print help message if there are no arguments.
if [[ "$#" -lt 1 ]]; then
  echo "Usage: $script [--watch] <MARKDOWN-FILE> [PANDOC-OPTIONS]"
  exit 1
fi

# Clone repositorty with custom pandoc scripts and filters if it was not
# cloned before.
if ! [ -d "$pandoc_scripts_dir" ]; then
  git clone https://just95@bitbucket.org/just95/pandoc-scripts.git "$pandoc_scripts_dir"
fi

# Optionally typeset the file whenever it is changed.
typeset_mode="typeset"
if [ "$1" == "--watch" ]; then
  shift
  typeset_mode="watch"
fi

# Forward all arguments.
"$pandoc_scripts_dir/$typeset_mode.sh" "$@"
